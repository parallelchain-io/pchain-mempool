/*
    Copyright © 2023, ParallelChain Lab
    Licensed under the Apache License, Version 2.0: http://www.apache.org/licenses/LICENSE-2.0
*/

//! `pchain-mempool` is an implementation of a [Mempool](Mempool):
//! the data structure that ParallelChain protocol replicas use to store pending transactions.
//! 
//! This crate is used by Fullnode and would maintain a global list of pending transactions across the network.
//! The functionalities of `pchain_mempool` are:
//! 1. **Inserting Transactions**: Insert submitted transactions into the Mempool.
//! 2. **Popping Transactions**: Remove and return the transaction from the Mempool to include it in a Block.
//! 3. **Removing Transactions**: Remove transaction(s) randomly to reduce Mempool's size to a `target_size`.
//! 
//! # Example
//! ```ignore
//! let mempool = Mempool::new(committed_nonce_provider, 1e10 as u64);
//! let insert_result = mempool.insert(txn);
//! 
//! let mempool_iterator = mempool.iter(min_base_fee_per_gas);
//! let popped_txn = mempool_iterator.next();
//! 
//! let removed_txns = mempool.remove_txns(5e9 as u64);
//! ```

use std::collections::{HashMap, BTreeMap};
use pchain_types::{
    cryptography::{PublicAddress, Sha256Hash},
    blockchain::{TransactionV1, TransactionV2},
    serialization::Serializable
};
use priority_queue::PriorityQueue;
use rand::{thread_rng, Rng};

pub type Nonce = u64;
type PriorityFee = u64;

/// [Mempool] stores the pending transactions waiting to be included in a Block
/// and provides management statistics.
pub struct Mempool<C: CommittedNonceProvider, T: Transaction> {
    // Transaction storage that maps transactions based on signer accounts,
    // and transactions of each signer are ordered by nonce increasingly.
    pub txns_from_accs: HashMap<PublicAddress, BTreeMap<Nonce, T>>,
    // List of signer accounts, in descending order of 
    // their first transaction (smallest nonce)'s `priority_fee_per_gas`.
    pub accs_ranked_by_priority_fee: PriorityQueue<PublicAddress, PriorityFee>,
    // Provider of committed nonces. 
    // [Insert](Mempool::insert) uses this to reject transactions with nonces
    // smaller than the signer's current committed nonce.
    pub committed_nonce_provider: C,
    // Number of transactions currently stored in the Mempool.
    pub num_of_txns: u64,
    // Total size of all transactions currently stored in the Mempool.
    pub size_in_bytes: u64,
    // The configured "never-exceed size" of the Mempool.
    // [Insert](Mempool::insert) rejects transactions that,
    // if inserted, will cause the Mempool to exceed this size.
    pub max_size_in_bytes: u64
}

impl<C: CommittedNonceProvider, T: Transaction> Mempool<C, T> {
    /// Creates an empty `Mempool` with provided `committed_nonce_provider` and `max_size_in_bytes`.
    pub fn new(committed_nonce_provider: C, max_size_in_bytes: u64) -> Mempool<C, T> {
        Mempool { 
            txns_from_accs: HashMap::new(), 
            accs_ranked_by_priority_fee: PriorityQueue::new(), 
            committed_nonce_provider, 
            num_of_txns: 0, 
            size_in_bytes: 0, 
            max_size_in_bytes 
        }
    }

    /// Inserts the transaction into Mempool.
    /// 
    /// Preliminary checking is performed during insertion. If it fails,
    /// a specific `InsertError` will be returned.
    /// 
    /// If the signer has signed another transaction with the same nonce
    /// as the inserted transaction, Mempool will replace the inserted transaction
    /// with the existing one, and return the old transaction wrapped in `Ok`.
    /// 
    /// When the nonce of the inserted transaction is new for the signer, Mempool 
    /// inserts the transaction and returns `Ok(None)`.
    pub fn insert(&mut self, txn: T) -> Result<Option<T>, InsertError> {
        // Check whether inserting current transaction will exceed the maximum size of Mempool.
        let txn_size_in_bytes = txn.size();
        if self.size_in_bytes.saturating_add(txn_size_in_bytes) > self.max_size_in_bytes {
            return Err(InsertError::MempoolIsFull);
        }

        // Check whether the nonce of current transaction is less than the committed nonce.
        if self.committed_nonce_provider.get(txn.signer()) > txn.nonce() {
            return Err(InsertError::NonceLTCommitted);
        }

        let mut insertion_result = None;

        // There is an existing BTreeMap of transactions from the same signer in the Mempool.
        if let Some(signer_txns) = self.txns_from_accs.get_mut(&txn.signer()) {
            // Check whether there is identical transaction existing in the Mempool.
            if let Some(txn_with_same_nonce) = signer_txns.get(&txn.nonce()){
                if txn_with_same_nonce.hash() == txn.hash() {
                    return Err(InsertError::DuplicateTransaction);
                }
            }
            
            insertion_result = signer_txns.insert(txn.nonce(), txn);

            // Update the `accs_ranked_by_priority_fee` due to
            // possible change of the transaction with the smallest nonce. 
            let updated_entry_txn = signer_txns
                .first_key_value()
                .unwrap()
                .1;
            self
                .accs_ranked_by_priority_fee
                .change_priority(
                    &updated_entry_txn.signer(), 
                    updated_entry_txn.priority_fee_per_gas()
                );
        } else {
            // There is no transaction from the same signer in the Mempool.

            let signer = txn.signer();
            let txn_priority_fee = txn.priority_fee_per_gas();

            let mut signer_txns = BTreeMap::new();
            signer_txns.insert(txn.nonce(), txn);

            self
                .txns_from_accs
                .insert(signer, signer_txns);
            self
                .accs_ranked_by_priority_fee
                .push(signer, txn_priority_fee);
        }

        if insertion_result.is_none() {
            self.num_of_txns += 1;
            self.size_in_bytes += txn_size_in_bytes;
        }

        Ok(insertion_result)
    }

    /// Removes and returns the next transaction available to be popped from the Mempool by using [MempoolIterator](MempoolIterator).
    /// Recommend to use this method
    /// if it is intentional to only pop the transaction using `min_base_fee_per_gas` once.
    pub fn pop(&mut self, min_base_fee_per_gas: u64) -> Option<T> {
        let mut mempool_iterator = self.iter(min_base_fee_per_gas);
        mempool_iterator.next()
    }

    /// Returns the [MempoolIterator](MempoolIterator) to be called for the next transaction to be popped from the Mempool.
    /// Recommend to use this method 
    /// if it is intentional to pop transactions using the same `min_base_fee_per_gas` multiple times.
    pub fn iter(&mut self, min_base_fee_per_gas: u64) -> MempoolIterator<'_, C, T> {
        MempoolIterator { 
            mempool: self, 
            signer_priority_to_be_reinserted: Vec::new(),
            min_base_fee_per_gas 
        }
    }

    /// Removes transaction(s) randomly from the Mempool until its size is reduced to `target_size`.
    pub fn remove_txns(&mut self, target_size: u64) -> Option<Vec<T>>{
        let mut dropped_txns = Vec::new();
        let mut signers = self
            .txns_from_accs
            .keys()
            .copied()
            .collect::<Vec<PublicAddress>>();

        while self.size_in_bytes > target_size {
            // Randomly select a signer account for removal.
            let selected_index = thread_rng().gen_range(0..signers.len());
            let selected_signer = signers[selected_index];

            let signer_txns = self
                .txns_from_accs
                .get_mut(&selected_signer)
                .unwrap();

            let dropped_txn = signer_txns
                .pop_last()
                .unwrap()
                .1;

            // SAFETY: remove the empty BTreeMap from Mempool and
            // the corresponding signer from `accs_ranked_by_priority_fee` and `signers`.
            if signer_txns.is_empty() {
                self
                    .txns_from_accs
                    .remove(&selected_signer);
                self
                    .accs_ranked_by_priority_fee
                    .remove(&selected_signer);
                signers.swap_remove(selected_index);
            }
            
            self.num_of_txns -= 1;
            self.size_in_bytes -= dropped_txn.size();
            dropped_txns.push(dropped_txn);
        }

        if dropped_txns.is_empty() {
            None
        } else {
            Some(dropped_txns)
        }
    }
}

/// [MempoolIterator] provides the next transaction available to be popped from Mempool.
pub struct MempoolIterator<'a, C: CommittedNonceProvider, T: Transaction> {
    /// A mutable reference to Mempool with certain lifetime.
    pub mempool: &'a mut Mempool<C, T>,
    /// A set of skipped (signer account, first transaction with smallest nonce's `priority_fee_per_gas`)
    /// for not fulfilling the `min_base_fee_per_gas` requirement from the Mempool to be re-inserted back
    /// for future usage.
    pub signer_priority_to_be_reinserted: Vec<(PublicAddress, PriorityFee)>,
    /// The `min_base_fee_per_gas` requirement from the Mempool.
    pub min_base_fee_per_gas: u64,
}

impl<'a, C: CommittedNonceProvider, T: Transaction> Iterator for MempoolIterator<'a, C, T> {
    type Item = T;

    /// Removes and returns the next transaction with the highest `priority_fee_per_gas`
    /// that has a `base_fee_per_gas` higher than `min_base_fee_per_gas` from the Mempool.
    /// 
    /// Returns None when no transaction available from the Mempool.
    fn next(&mut self) -> Option<Self::Item> {
        if self.mempool.num_of_txns == 0 {
            return None;
        }

        let mut popped_transaction = None;

        // Pop the signer account in the descending order of `priority_fee_per_gas` of transaction.
        while let Some((signer, entry_txn_priority_fee)) = self.mempool.accs_ranked_by_priority_fee.pop() {
            let signer_txns = self
                .mempool
                .txns_from_accs
                .get_mut(&signer)
                .unwrap();
            
            // Pop the transaction that fulfils the `min_base_fee_per_gas` requirement from the Mempool.
            if signer_txns.first_key_value().unwrap().1.max_base_fee_per_gas() >= self.min_base_fee_per_gas {
                let popped_txn = signer_txns.pop_first()
                    .unwrap()
                    .1;

                // SAFETY: remove the empty BTreeMap from Mempool.
                if signer_txns.is_empty() {
                    self
                        .mempool
                        .txns_from_accs
                        .remove(&signer);
                } else {
                    let new_entry_txn = signer_txns.first_key_value().unwrap().1;
                    if new_entry_txn.max_base_fee_per_gas() < self.min_base_fee_per_gas {
                        self.signer_priority_to_be_reinserted.push((signer, new_entry_txn.priority_fee_per_gas()));
                    } else {
                        self
                            .mempool
                            .accs_ranked_by_priority_fee
                            .push(signer, new_entry_txn.priority_fee_per_gas());
                    }
                }

                self.mempool.num_of_txns -= 1;
                self.mempool.size_in_bytes -= popped_txn.size();
                popped_transaction = Some(popped_txn);

                break;
            } else {
                // Store the popped signer accounts with corresponding `priority_fee_per_gas` of entry transaction,
                // which fail to fulfil the current `min_base_fee_per_gas` requirement from the Mempool.
                self.signer_priority_to_be_reinserted.push((signer, entry_txn_priority_fee));
            }
        }

        popped_transaction
    }
}

impl<'a, C: CommittedNonceProvider, T: Transaction> Drop for MempoolIterator<'a, C, T> {
    /// Re-inserts tuples in `signer_priority_to_be_reinserted` before dropping the [MempoolIterator](MempoolIterator).
    fn drop(&mut self) {
        // Re-insert the popped tuples (`signer`, `priority_fee_per_gas`) back into `accs_ranked_by_priority_fee`
        // for being checked against future (possibly) lower `min_base_fee_per_gas` requirement from the Mempool.
        for (signer, entry_txn_priority_fee) in self.signer_priority_to_be_reinserted.iter().copied() {
            self
                .mempool
                .accs_ranked_by_priority_fee
                .push(signer, entry_txn_priority_fee);
        }
    }
}

/// An implementation of [Transaction] can provide methods 
/// that fulfil the Mempool's core functionalities: insert, pop, and remove transactions. 
pub trait Transaction: Send + Clone + 'static {
    /// Returns the signer address of current transaction.
    fn signer(&self) -> PublicAddress;
    /// Returns the nonce of current transaction.
    fn nonce(&self) -> u64;
    /// Returns the `max_base_fee_per_gas` of current transaction.
    fn max_base_fee_per_gas(&self) -> u64;
    /// Returns the `priority_fee_per_gas` of current transaction.
    fn priority_fee_per_gas(&self) -> u64;
    /// Returns the hash of current transaction.
    fn hash(&self) -> Sha256Hash;
    /// Returns the size of current transaction in bytes.
    fn size(&self) -> u64;
}

impl Transaction for TransactionV1 {
    fn signer(&self) -> PublicAddress {
        self.signer
    }

    fn nonce(&self) -> u64 {
        self.nonce
    }

    fn max_base_fee_per_gas(&self) -> u64 {
        self.max_base_fee_per_gas
    }

    fn priority_fee_per_gas(&self) -> u64 {
        self.priority_fee_per_gas
    }

    fn hash(&self) -> Sha256Hash {
        self.hash
    }

    fn size(&self) -> u64 {
        TransactionV1::serialize(self).len() as u64
    }
}

impl Transaction for TransactionV2 {
    fn signer(&self) -> PublicAddress {
        self.signer
    }

    fn nonce(&self) -> u64 {
        self.nonce
    }

    fn max_base_fee_per_gas(&self) -> u64 {
        self.max_base_fee_per_gas
    }

    fn priority_fee_per_gas(&self) -> u64 {
        self.priority_fee_per_gas
    }

    fn hash(&self) -> Sha256Hash {
        self.hash
    }

    fn size(&self) -> u64 {
        TransactionV2::serialize(self).len() as u64
    }
}


/// An implementation of [CommittedNonceProvider] can retrieve nonce of a specific signer account
/// from corresponding storage.
pub trait CommittedNonceProvider: Send + Clone + 'static {
    /// Returns the nonce of the provided signer account.
    fn get(&self, signer: PublicAddress) -> Nonce;
}

/// [InsertError] indicates the possible errors during transaction insertion in the Mempool.
#[derive(Debug, PartialEq)]
pub enum InsertError {
    /// The signer account in Mempool has the same transaction.
    DuplicateTransaction,
    /// Inserting current transaction will exceed Mempool's maximum size in bytes. 
    MempoolIsFull,
    /// The transaction's nonce is lower than this Mempool's view of the committed nonce.
    NonceLTCommitted
}