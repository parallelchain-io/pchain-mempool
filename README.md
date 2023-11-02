# ParallelChain Mempool

ParallelChain Mempool is an implementation of the data structure "mempool" that ParallelChain protocol replicas use to store a global list of pending transactions. The implementation of mempool supports three functionalities: inserting submitted transactions into the mempool, removing and returning the transaction from the mempool to include it in a block, and removing transaction(s) randomly to reduce mempool's size.

## Basic usage
```rust
// Here demonstrate how to instantiate the Mempool, 
// and realize three functionalities of the mempool.

// Step 1. prepare a data structure that implements the CommittedNonceProvider trait.
let max_mempool_size = 1e10 as u64;
let mempool = Mempool::new(committed_nonce_provider, max_mempool_size);

// Step 2. prepare the transaction and insert it into the mempool.
let _insert_result = mempool.insert(transaction);

// Step 3. remove and return the transaction to include it in a block.
let mempool_iterator = mempool.iter(min_base_fee_per_gas);
let popped_transaction = mempool_iterator.next();

// Step 4. remove transaction(s) randomly to a "target size".
let target_size = 5e9 as u64;
let removed_txns = mempool.remove_txns(target_size);
```

## Versioning
Current version of the library is 0.1.0. Patch version increases are not guaranteed to be non-breaking.

## Opening an issue

Open an issue in GitHub if you:
1. Have a feature request / feature idea,
2. Have any questions (particularly software related questions),
3. Think you may have discovered a bug.

Please try to label your issues appropriately.