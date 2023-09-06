/*
    Copyright © 2023, ParallelChain Lab
    Licensed under the Apache License, Version 2.0: http://www.apache.org/licenses/LICENSE-2.0
*/

//! The test suite for `pchain-mempool` utilizes the [Mempool](pchain_mempool::Mempool) to test insert transactions,
//! pop transactions and remove transactions.
//! 
//! The mempool used in the test suite uses a [TestNonceProvider](TestNonceProvider), which sets the committed nonces for 
//! different signer accounts manually.
//! 
//! There are 7 tests currently:
//! 1. [mempool_insert_iter_remove_txnv1_success()]: tests three implemented methods of the Mempool: insert, iter and remove
//!    transactions. This test aims to perform all three methods successfully by using
//!    pchain_types::blockchain::TransactionV1.
//! 2. [mempool_insert_pop_remove_txnv2_success]: tests three implemented methods of the Mempool: insert, pop and remove 
//!    transactions. This test aims to perform all three methods successfully by using
//!    pchain_types::blockchain::TransactionV2.
//! 3. [mempool_update_same_nonce_txn]: tests inserting two transactions from the same signer with the same nonce but different
//!    hash. The first transaction would be updated by the second transaction and returned.
//! 4. [mempool_reject_duplicate_txn]: tests inserting a duplicate transaction, which would be rejected by
//!    [insert](pchain_mempool::Mempool::insert) method with "DuplicateTransaction" exception.
//! 5. [mempool_reject_full]: tests inserting a transaction that would cause the Mempool to exceed its `max_size`, which would
//!    be rejected by [insert](pchain_mempool::Mempool::insert) method with "MempoolIsFull" exception.
//! 6. [mempool_reject_low_nonce]: tests inserting a transaction with nonce smaller than the signer account's committed nonce,
//!    which would be rejected by [insert](pchain_mempool::Mempool::insert) method with "NonceLTCommitted" exception.
//! 7. [mempool_iter_low_base_fee]: tests popping the transaction from the Mempool with `min_base_fee_per_gas` larger than
//!    all the transactions' `base_fee_per_gas` in the Mempool, which would obtain a None from the 
//!    [pop](pchain_mempool::Mempool::iter) method.

use std::{
    collections::HashMap,
    mem::ManuallyDrop,
};
use pchain_types::{
    cryptography::{PublicAddress, Keypair},
    blockchain::{TransactionV1, TransactionV2},
};
use pchain_mempool::{
    Mempool, 
    InsertError, 
    CommittedNonceProvider, 
    Transaction,
    Nonce,
};

use crate::test_accounts::*;

#[test]
fn mempool_insert_iter_remove_txnv1_success() {
    let test_nonce_provider = TestNonceProvider::default();
    let mut mempool = Mempool::new(test_nonce_provider, 1e10 as u64);

    // Initialize dummy transactions from two signer accounts.
    // `size_in_bytes` of each transaction is 164.
    let txn1_account1 = TransactionV1::new(
        &Keypair::from_keypair_bytes(&ORIGIN1_KEYPAIR_BYTES).expect("Failed to genearte keypair from given byte array."), 
        6, 
        Vec::new(), 
        67_500_000, 
        8, 
        100
    );
    let txn2_account1 = TransactionV1::new(
        &Keypair::from_keypair_bytes(&ORIGIN1_KEYPAIR_BYTES).expect("Failed to genearte keypair from given byte array."), 
        3, 
        Vec::new(), 
        67_500_000, 
        8, 
        50
    );
    let txn1_account2 = TransactionV1::new(
        &Keypair::from_keypair_bytes(&ORIGIN2_KEYPAIR_BYTES).expect("Failed to genearte keypair from given byte array."), 
        1, 
        Vec::new(), 
        67_500_000, 
        8, 
        20
    );
    let txn2_account2 = TransactionV1::new(
        &Keypair::from_keypair_bytes(&ORIGIN2_KEYPAIR_BYTES).expect("Failed to genearte keypair from given byte array."), 
        2, 
        Vec::new(), 
        67_500_000, 
        8, 
        40
    );
    assert!(mempool.insert(txn1_account1).is_ok());
    assert!(mempool.insert(txn2_account1).is_ok());
    assert!(mempool.insert(txn1_account2).is_ok());
    assert!(mempool.insert(txn2_account2).is_ok());

    assert_eq!(mempool.num_of_txns, 4);

    let mut mempool_iterator = mempool.iter(8);
    let popped_txn1 = mempool_iterator.next();
    assert!(popped_txn1.is_some());
    let popped_txn1 = popped_txn1.unwrap();
    assert_eq!(popped_txn1.nonce(), 3);
    assert_eq!(popped_txn1.priority_fee_per_gas(), 50);

    let popped_txn2 = mempool_iterator.next();
    assert!(popped_txn2.is_some());
    let popped_txn2 = popped_txn2.unwrap();
    assert_eq!(popped_txn2.nonce(), 6);
    assert_eq!(popped_txn2.priority_fee_per_gas(), 100);
    let _dropped_iterator = ManuallyDrop::new(mempool_iterator);
    assert_eq!(mempool.num_of_txns, 2);

    assert!(mempool.size_in_bytes == 328);
    mempool.remove_txns(300);
    assert_eq!(mempool.num_of_txns, 1);
    assert!(mempool.size_in_bytes <= 300);
}
#[test]
fn mempool_insert_pop_remove_txnv2_success() {
    let test_nonce_provider = TestNonceProvider::default();
    let mut mempool = Mempool::new(test_nonce_provider, 1e10 as u64);

    // Initialize dummy transactions from two signer accounts.
    // `size_in_bytes` of each transaction is 164.
    let txn1_account1 = TransactionV2::new(
        &Keypair::from_keypair_bytes(&ORIGIN1_KEYPAIR_BYTES).expect("Failed to genearte keypair from given byte array."), 
        3, 
        Vec::new(), 
        67_500_000, 
        8, 
        50
    );
    let txn1_account2 = TransactionV2::new(
        &Keypair::from_keypair_bytes(&ORIGIN2_KEYPAIR_BYTES).expect("Failed to genearte keypair from given byte array."), 
        1, 
        Vec::new(), 
        67_500_000, 
        8, 
        20
    );

    assert!(mempool.insert(txn1_account1).is_ok());
    assert!(mempool.insert(txn1_account2).is_ok());
    
    assert_eq!(mempool.num_of_txns, 2);

    let popped_txn = mempool.pop(8);
    assert!(popped_txn.is_some());
    let popped_txn = popped_txn.unwrap();
    assert_eq!(popped_txn.nonce(), 3);
    assert_eq!(popped_txn.priority_fee_per_gas(), 50);
    assert_eq!(mempool.num_of_txns, 1);

    assert!(mempool.size_in_bytes == 164);
    mempool.remove_txns(100);
    assert_eq!(mempool.num_of_txns, 0);
    assert!(mempool.size_in_bytes <= 100);
}

#[test]
fn mempool_update_same_nonce_txn() {
    let test_nonce_provider = TestNonceProvider::default();
    let mut mempool = Mempool::new(test_nonce_provider, 1e10 as u64);

    // Initialize transactions from the same signer account with the same nonce but different hash.
    let txn1_account1 = TransactionV1::new(
        &Keypair::from_keypair_bytes(&ORIGIN1_KEYPAIR_BYTES).expect("Failed to genearte keypair from given byte array."), 
        2, 
        Vec::new(), 
        67_500_000, 
        8, 
        100
    );
    let txn2_account1 = TransactionV1::new(
        &Keypair::from_keypair_bytes(&ORIGIN1_KEYPAIR_BYTES).expect("Failed to genearte keypair from given byte array."), 
        2, 
        Vec::new(), 
        67_500_000, 
        10, 
        50
    );

    assert!(mempool.insert(txn1_account1.clone()).is_ok());
    assert_eq!(mempool.num_of_txns, 1);

    assert_eq!(mempool.insert(txn2_account1).unwrap().unwrap().hash(), txn1_account1.hash());
    assert_eq!(mempool.num_of_txns, 1);
}

#[test]
fn mempool_reject_duplicate_txn() {
    let test_nonce_provider = TestNonceProvider::default();
    let mut mempool = Mempool::new(test_nonce_provider, 1e10 as u64);

    // Initialize identical transactions from the same signer account.
    let txn1_account1 = TransactionV1::new(
        &Keypair::from_keypair_bytes(&ORIGIN1_KEYPAIR_BYTES).expect("Failed to genearte keypair from given byte array."), 
        2, 
        Vec::new(), 
        67_500_000, 
        8, 
        100
    );
    let txn2_account1 = TransactionV1::new(
        &Keypair::from_keypair_bytes(&ORIGIN1_KEYPAIR_BYTES).expect("Failed to genearte keypair from given byte array."), 
        2, 
        Vec::new(), 
        67_500_000, 
        8, 
        100
    );

    assert!(mempool.insert(txn1_account1).is_ok());
    assert_eq!(mempool.num_of_txns, 1);

    assert_eq!(mempool.insert(txn2_account1).err().unwrap(), InsertError::DuplicateTransaction);
}

#[test]
fn mempool_reject_full() {
    let test_nonce_provider = TestNonceProvider::default();
    let mut mempool = Mempool::new(test_nonce_provider, 300 as u64);

    // Initialize dummy transactions having byte size of 164 each from the same signer account.
    let txn1_account1 = TransactionV1::new(
        &Keypair::from_keypair_bytes(&ORIGIN1_KEYPAIR_BYTES).expect("Failed to genearte keypair from given byte array."), 
        2, 
        Vec::new(), 
        67_500_000, 
        8, 
        100
    );
    let txn2_account1 = TransactionV1::new(
        &Keypair::from_keypair_bytes(&ORIGIN1_KEYPAIR_BYTES).expect("Failed to genearte keypair from given byte array."), 
        3, 
        Vec::new(), 
        67_500_000, 
        8, 
        80
    );

    assert!(mempool.insert(txn1_account1).is_ok());

    assert_eq!(mempool.insert(txn2_account1).err().unwrap(), InsertError::MempoolIsFull);
}

#[test]
fn mempool_reject_low_nonce() {
    let test_nonce_provider = TestNonceProvider::default();
    let mut mempool = Mempool::new(test_nonce_provider, 1e10 as u64);

    // Initialize dummy transaction of signer account with committed nonce 2.
    let txn1_account1 = TransactionV1::new(
        &Keypair::from_keypair_bytes(&ORIGIN1_KEYPAIR_BYTES).expect("Failed to genearte keypair from given byte array."), 
        1, 
        Vec::new(), 
        67_500_000, 
        8, 
        100
    );

    assert_eq!(mempool.insert(txn1_account1).err().unwrap(), InsertError::NonceLTCommitted);
}

#[test]
fn mempool_iter_low_base_fee() {
    let test_nonce_provider = TestNonceProvider::default();
    let mut mempool = Mempool::new(test_nonce_provider, 1e10 as u64);

    // Initialize dummy transactions from different signer accounts with lower `max_base_fee_per_gas`.
    let txn1_account1 = TransactionV1::new(
        &Keypair::from_keypair_bytes(&ORIGIN1_KEYPAIR_BYTES).expect("Failed to genearte keypair from given byte array."), 
        3, 
        Vec::new(), 
        67_500_000, 
        6, 
        50
    );
    let txn1_account2 = TransactionV1::new(
        &Keypair::from_keypair_bytes(&ORIGIN2_KEYPAIR_BYTES).expect("Failed to genearte keypair from given byte array."), 
        4, 
        Vec::new(), 
        67_500_000, 
        3, 
        20
    );
    
    assert!(mempool.insert(txn1_account1).is_ok());
    assert!(mempool.insert(txn1_account2).is_ok());

    let mut mempool_iterator = mempool.iter(8);
    assert!(mempool_iterator.next().is_none());
    assert_eq!(mempool_iterator.signer_priority_to_be_reinserted.len(), 2);
    let _dropped_iterator = ManuallyDrop::new(mempool_iterator);
    assert_eq!(mempool.num_of_txns, 2);

}

/// [TestNonceProvider] defines the easy version storage to retrieve signer accounts' committed Nonce for testing.
#[derive(Clone)]
struct TestNonceProvider {
    signer_nonce: HashMap<PublicAddress, Nonce>,
}

impl TestNonceProvider {
    #[allow(dead_code)]
    fn default() -> TestNonceProvider {
        let mut test_nonce_provider = TestNonceProvider {
            signer_nonce: HashMap::new(),
        };

        test_nonce_provider.signer_nonce.insert(
            Keypair::from_keypair_bytes(&ORIGIN1_KEYPAIR_BYTES).expect("Failed to genearte keypair from given byte array.").verifying_key().to_bytes(), 
            2
        );
        test_nonce_provider.signer_nonce.insert(
            Keypair::from_keypair_bytes(&ORIGIN2_KEYPAIR_BYTES).expect("Failed to genearte keypair from given byte array.").verifying_key().to_bytes(), 
            1
        );
        test_nonce_provider
    }
}

impl CommittedNonceProvider for TestNonceProvider {
    /// Retrieves the committed nonce of specific signer account.
    fn get(&self, from_addr: PublicAddress) -> Nonce {
        *self.signer_nonce.get(&from_addr).unwrap()
    }
}
/// Test Accounts
/// Signing and submitting a transaction could be required for a test.
/// The following accounts' keypair information can be used accordingly.
#[allow(dead_code)]
pub(crate) mod test_accounts {
    // Origin Account 1.
    pub(crate) const ORIGIN1_KEYPAIR_BYTES: [u8; 64] = [242, 59, 201, 56, 146, 89, 242, 34, 149, 218, 26, 63, 157, 146, 122, 76, 209, 187, 131, 51, 2, 130, 176, 202, 179, 231, 20, 245, 31, 0, 58, 45, 246, 155, 204, 250, 131, 19, 26, 24, 209, 54, 68, 194, 134, 74, 68, 28, 222, 213, 128, 152, 149, 189, 242, 249, 214, 170, 246, 215, 217, 15, 238, 95];

    // Origin Account 2.
    pub(crate) const ORIGIN2_KEYPAIR_BYTES: [u8; 64] =  [96, 160, 230, 237, 57, 0, 109, 193, 153, 147, 23, 250, 98, 14, 194, 254, 111, 2, 233, 220, 146, 103, 66, 59, 188, 230, 180, 127, 189, 30, 235, 115, 22, 220, 186, 232, 159, 237, 145, 180, 247, 61, 137, 244, 60, 103, 187, 152, 247, 88, 133, 131, 89, 205, 100, 97, 61, 153, 192, 182, 122, 37, 16, 255];

    // Target Account.
    pub(crate) const TARGET_KEYPAIR_BYTES: [u8; 64] = [20, 104, 249, 224, 5, 53, 88, 147, 149, 18, 209, 182, 247, 189, 237, 83, 16, 104, 214, 171, 227, 12, 5, 36, 171, 213, 151, 72, 8, 129, 198, 71, 246, 40, 94, 22, 194, 138, 172, 236, 102, 148, 191, 245, 227, 142, 32, 103, 170, 78, 80, 108, 26, 45, 255, 58, 140, 233, 198, 73, 151, 223, 237, 95];
}