//! Transaction pool management module.
//!
//! This module contains the core components and functionality for managing a transaction pool.
//! It includes submodules for handling different aspects of the pool, such as pending transactions,
//! queued transactions, and overall pool state management.
//!
//! The main components of this module are:
//!
//! - `Pool`: The central struct that manages the entire transaction pool.
//! - `PoolConfig`: Configuration parameters for the transaction pool.
//! - Various submodules (`all`, `pending`, `queued`, `state`, `sequence`) that handle specific
//!   aspects of pool management.
//!
//! This module provides functionality for adding transactions to the pool
//! and retrieving them in an optimal order for block inclusion.

pub mod all;
pub mod pending;
pub mod queued;
pub mod sequence;
pub mod state;

use std::collections::btree_map::Entry;
use std::sync::Arc;

use alloy::{
    consensus::{Signed, Transaction, TxEip1559, TxEnvelope},
    primitives::{aliases::TxHash, Address, B256, U256},
};

use crate::{
    identifiers::TransactionId,
    ordering::TransactionOrdering,
    pool::{
        all::AllTransactions,
        pending::PendingPool,
        queued::QueuedPool,
        sequence::TransactionSequence,
        state::{SubPool, TxState},
    },
    result::{
        AddedPendingTransaction, AddedTransaction, Destination, InsertErr, InsertOk, InsertResult,
        PoolError, PoolErrorKind, PoolResult, PoolUpdate, UpdateOutcome,
    },
};

/// Configuration parameters for the transaction pool.
///
/// This struct defines various limits and settings that control the behavior of the transaction pool.
///
/// # Fields
///
/// * `max_account_slots`: The maximum number of transactions a single account can have in the pool.
///   This helps prevent spam and ensures fair access to the pool for all users.
///
/// * `block_gas_limit`: The maximum amount of gas that can be used in a single block. This is used
///   to limit the selection of transactions for inclusion in a block.
///
/// * `minimal_protocol_basefee`: The minimum base fee required by the protocol. Transactions with
///   a lower base fee than this will never be included in the chain.
///
/// * `pending_base_fee`: The expected base fee for the pending block. This is used in calculations
///   related to transaction prioritization and fee estimation.

#[derive(Debug, Clone)]
pub struct PoolConfig {
    /// Max number of transactions a user can have in the pool
    pub max_account_slots: usize,
    /// The gas limit of the block
    pub block_gas_limit: u64,
    /// Minimum base fee required by the protocol.
    ///
    /// Transactions with a lower base fee will never be included by the chain
    pub minimal_protocol_basefee: u64,
    /// Expected base fee for the pending block
    pub pending_base_fee: u64,
}

/// A transaction pool that manages and orders transactions for inclusion in blocks.
///
/// The `Pool` struct is the central component of the transaction sequencing system. It manages
/// the lifecycle and organization of transactions, separating them into pending and queued pools.
/// The pool is generic over a transaction ordering type `O`, allowing for flexible prioritization
/// strategies.
///
/// # Type Parameters
///
/// * `O`: A type implementing `TransactionOrdering`, which defines how transactions are prioritized.
///
/// # Fields
///
/// * `config`: Configuration parameters for the pool.
/// * `all_transactions`: A collection of all validated transactions in the pool.
/// * `pending_transactions`: Manages transactions that are ready for inclusion in a block.
/// * `queued_transactions`: Holds transactions that are waiting for their prerequisites to be met.
///
/// This structure provides methods for adding transactions and retrieving optimal transaction
/// sequences.
#[derive(Debug, Clone)]
pub struct Pool<O>
where
    O: TransactionOrdering,
{
    /// Configuration parameters for the pool
    config: PoolConfig,
    /// All transactions in the pool, grouped by sender, ordered by nonce
    all_transactions: AllTransactions,
    ///All transactions that can be executed on the current chain state
    pending_transactions: PendingPool<O>,
    /// All transactions that cannot be executed on current state but might be able to in the future
    queued_transactions: QueuedPool,
}

impl<O> Pool<O>
where
    O: TransactionOrdering,
{
    /// Creates a new `Pool` instance with the given configuration and ordering strategy.
    ///
    /// This function initializes a new transaction pool with the specified configuration and
    /// transaction ordering mechanism. The pool is responsible for managing incoming transactions,
    /// organizing them into appropriate sub-pools (pending and queued), and providing an efficient
    /// way to retrieve transactions for block production.
    ///
    /// # Arguments
    ///
    /// * `config` - A `PoolConfig` struct containing the configuration parameters for the pool,
    ///   such as maximum account slots, block gas limit, and base fee settings.
    /// * `ordering` - An instance of a type implementing the `TransactionOrdering` trait, which
    ///   defines how transactions should be prioritized within the pool.
    ///
    /// # Returns
    ///
    /// Returns a new `Pool<O>` instance, where `O` is the type implementing `TransactionOrdering`.
    ///
    /// # Example
    ///
    /// ```
    /// use t1_sequencer_project::{Pool, PoolConfig, CoinbaseTipOrdering};
    /// use alloy::consensus::TxEnvelope;
    ///
    /// let config = PoolConfig {
    ///     max_account_slots: 16,
    ///     block_gas_limit: 30_000_000,
    ///     minimal_protocol_basefee: 1_000_000_000,
    ///     pending_base_fee: 1_500_000_000,
    /// };
    /// let ordering: CoinbaseTipOrdering<TxEnvelope> = CoinbaseTipOrdering::default();
    /// let pool = Pool::new(config, ordering);
    /// ```
    ///
    /// # Note
    ///
    /// The choice of ordering strategy will impact the behavior of the
    /// transaction pool. Ensure that the selected ordering mechanism aligns with the desired
    /// prioritization logic for your implementation.
    pub fn new(config: PoolConfig, ordering: O) -> Self {
        Self {
            config,
            all_transactions: AllTransactions::default(),
            pending_transactions: PendingPool::new(ordering),
            queued_transactions: QueuedPool::default(),
        }
    }

    /// Adds a new transaction to the pool.
    ///
    /// This function attempts to add a new transaction to the pool, performing various checks
    /// and updates in the process. It handles the following steps:
    ///
    /// 1. Checks if the transaction already exists in the pool.
    /// 2. Validates the transaction, considering on-chain balance and nonce.
    /// 3. If successful, updates the pool state, including potential replacements and promotions.
    /// 4. Handles various error conditions that may occur during the insertion process.
    ///
    /// # Arguments
    ///
    /// * `tx` - The transaction to be added, Alloy `TxEnvelope` type.
    /// * `on_chain_balance` - The current on-chain balance of the sender's account.
    /// * `on_chain_nonce` - The current on-chain nonce of the sender's account.
    ///
    /// # Returns
    ///
    /// Returns a `PoolResult<AddedTransaction>`, which is:
    /// - `Ok(AddedTransaction)` if the transaction was successfully added. This includes
    ///   information about whether the transaction was added to the pending or queued pool,
    ///   any transactions that were promoted or discarded as a result, and any transaction
    ///   that was replaced.
    /// - `Err(PoolError)` if the transaction could not be added, with details about the error.
    ///
    /// # Errors
    ///
    /// This function can return errors for various reasons, including:
    /// - The transaction already exists in the pool.
    /// - The transaction type is unknown.
    /// - The transaction nonce is invalid.
    /// - There's an issue with the transaction signature.
    pub fn add_transaction(
        &mut self,
        tx: TxEnvelope,
        on_chain_balance: U256,
        on_chain_nonce: u64,
    ) -> PoolResult<AddedTransaction> {
        let tx_hash = *tx.tx_hash();
        
        // Early return if transaction exists
        if self.contains(&tx_hash) {
            return Err(PoolError::new(tx_hash, PoolErrorKind::AlreadyImported));
        }

        // Insert the transaction or convert InsertErr to PoolError using a helper function
        match self.insert_tx(tx, on_chain_balance, on_chain_nonce) {
            Ok(insert_ok) => self.process_insert_ok(insert_ok),
            Err(err) => Err(self.convert_insert_error(err, tx_hash)),
        }
    }

    /// Returns an iterator over the sequence of transactions in the pending pool.
    ///
    /// This method provides access to an ordered sequence of transactions that are ready to be
    /// executed against the current chain state. The returned iterator yields transactions in
    /// the order determined by the pool's transaction ordering strategy.
    ///
    /// # Returns
    ///
    /// Returns a `TransactionSequence<O>` iterator, where `O` is the transaction ordering type
    /// used by this pool. This iterator will yield `Arc<TxEnvelope>` items representing the
    /// transactions.
    ///
    /// # Characteristics
    ///
    /// - The returned transactions are guaranteed to be in the pending pool, meaning they are
    ///   ready for immediate execution.
    /// - The order of transactions respects nonce ordering for each sender address.
    /// - The overall sequence is ordered according to the pool's `TransactionOrdering` implementation.
    ///
    /// # Usage
    ///
    /// This method is particularly useful for block producers or simulators that need to retrieve
    /// a sequence of transactions ready for inclusion in a block or for simulating state transitions.
    ///
    /// # Example
    ///
    /// ```
    /// use alloy::{
    ///     consensus::TxEnvelope,
    ///     network::{Ethereum, EthereumWallet, NetworkWallet},
    ///     primitives::{Address, U256, TxKind},
    ///     rpc::types::TransactionRequest,
    ///     signers::{
    ///         k256::Secp256k1,
    ///         local::LocalSigner,
    ///         utils::secret_key_to_address,
    ///     },
    /// };
    /// use ecdsa::SigningKey;
    /// use rand_core::OsRng;
    ///
    /// use t1_sequencer_project::{Pool, PoolConfig, CoinbaseTipOrdering};
    ///
    /// #[tokio::main]
    /// async fn main() {
    ///     // Create the pool config
    ///     let config = PoolConfig {
    ///         max_account_slots: 16,
    ///         block_gas_limit: 30_000_000,
    ///         minimal_protocol_basefee: 1,
    ///         pending_base_fee: 1,
    ///     };
    ///     
    ///     // Create the ordering strategy
    ///     let ordering: CoinbaseTipOrdering<TxEnvelope> = CoinbaseTipOrdering::default();
    ///
    ///     // Create the pool
    ///     let mut pool = Pool::new(config, ordering);
    ///
    ///     // Create the sender
    ///     let private_key = SigningKey::random(&mut OsRng);
    ///     let sender = secret_key_to_address(&private_key);
    ///
    ///     // Create the transaction request
    ///     let req = TransactionRequest {
    ///         from: None,
    ///         to: Some(TxKind::Call(Address::random())),
    ///         max_fee_per_gas: Some(20),
    ///         max_priority_fee_per_gas: Some(10),
    ///         gas: Some(100_000),
    ///         value: Some(U256::from(1)),
    ///         nonce: Some(0),
    ///         chain_id: Some(1),
    ///         ..Default::default()
    ///     };
    ///
    ///     // Build the typed transaction
    ///     let typed_tx = req.build_typed_tx().expect("Failed to build typed tx");
    ///
    ///     // Create the local signer
    ///     let local_signer: LocalSigner<SigningKey<Secp256k1>> = LocalSigner::from_signing_key(private_key);
    ///     let wallet = EthereumWallet::new(local_signer);
    ///
    ///     // Sign the transaction
    ///     let tx_env = <EthereumWallet as NetworkWallet<Ethereum>>::sign_transaction_from(&wallet, sender, typed_tx).await.unwrap();
    ///
    ///     // Create the on-chain balance and nonce
    ///     let on_chain_balance = U256::from(1_000_000_000);
    ///     let on_chain_nonce = 0;
    ///
    ///     // Add the transaction to the pool
    ///     let result = pool.add_transaction(tx_env, on_chain_balance, on_chain_nonce);
    ///
    ///     // Get the transaction sequence
    ///     let mut sequence = pool.transaction_sequence();
    ///     let tx = sequence.next().unwrap();
    /// }
    /// ```
    pub fn transaction_sequence(&self) -> TransactionSequence<O> {
        self.pending_transactions.transaction_sequence()
    }

    /// Checks if the given tx_hash is present in the all_transactions pool
    pub(crate) fn contains(&self, tx_hash: &TxHash) -> bool {
        self.all_transactions.contains(tx_hash)
    }

    /// Attempts to insert a transaction into the pool
    fn insert_tx(
        &mut self,
        transaction: TxEnvelope,
        on_chain_balance: U256,
        on_chain_nonce: u64,
    ) -> InsertResult {
        let transaction = Arc::new(transaction);
        let (_, unsigned_tx) = self.extract_tx_details(&transaction)?;
        let signer = self.recover_signer(&transaction)?;
        let tx_nonce = unsigned_tx.nonce;
        let gas_limit = unsigned_tx.gas_limit();

        let transaction_id = TransactionId {
            sender: signer,
            nonce: tx_nonce,
        };

        self.process_transaction(
            transaction.clone(),
            transaction_id,
            on_chain_balance,
            on_chain_nonce,
            tx_nonce,
            signer,
            gas_limit,
        )
    }

    /// Extracts the signed and unsigned transaction details
    fn extract_tx_details<'a>(
        &self,
        transaction: &'a Arc<TxEnvelope>,
    ) -> Result<(&'a Signed<TxEip1559>, &'a TxEip1559), InsertErr> {
        match &**transaction {
            TxEnvelope::Eip1559(signed_tx) => Ok((signed_tx, signed_tx.tx())),
            _ => Err(InsertErr::UnknownTransactionType),
        }
    }

    /// Recovers the signer of the transaction
    fn recover_signer(&self, transaction: &Arc<TxEnvelope>) -> Result<Address, InsertErr> {
        transaction
            .recover_signer()
            .map_err(|_| InsertErr::SignatureError)
    }

    /// Processes the transaction and updates the pool state
    fn process_transaction(
        &mut self,
        transaction: Arc<TxEnvelope>,
        transaction_id: TransactionId,
        on_chain_balance: U256,
        on_chain_nonce: u64,
        tx_nonce: u64,
        signer: Address,
        gas_limit: u64,
    ) -> InsertResult {
        // Initialize the transaction state
        let state =
            self.initialize_tx_state(&transaction, tx_nonce, on_chain_nonce, signer, gas_limit)?;
        let pool_tx = self.create_pool_tx(transaction.clone(), state);
        let replaced_tx = self.insert_or_replace_tx(transaction_id, pool_tx.clone())?;
        self.update_descendant_transactions(
            transaction_id,
            on_chain_balance,
            on_chain_nonce,
            tx_nonce,
            signer,
            pool_tx,
            replaced_tx,
        )
    }

    /// Initializes the transaction state after ensuring that the transaction is valid
    fn initialize_tx_state(
        &self,
        transaction: &Arc<TxEnvelope>,
        tx_nonce: u64,
        on_chain_nonce: u64,
        signer: Address,
        gas_limit: u64,
    ) -> Result<TxState, InsertErr> {
        // Ensure the transaction is valid
        let transaction = self.ensure_valid(
            Arc::clone(transaction),
            gas_limit,
            &signer,
            on_chain_nonce,
            tx_nonce,
        )?;

        // Initialize the transaction state
        let mut state = TxState::default();

        // Tx does not exceed block gas limit, checked in ensure_valid
        state.insert(TxState::NOT_TOO_MUCH_GAS);

        if !transaction.is_eip4844() {
            // Non-EIP4844 transaction always satisfy the blob fee cap condition
            state.insert(TxState::ENOUGH_BLOB_FEE_CAP_BLOCK);
        }

        let ancestor = TransactionId::ancestor(tx_nonce, on_chain_nonce, signer);
        // If there's no ancestor tx then this is the next transaction to be executed
        if ancestor.is_none() {
            state.insert(TxState::NO_NONCE_GAPS);
            state.insert(TxState::NO_PARKED_ANCESTORS);
        }

        // Check dynamic fee
        let fee_cap = transaction.max_fee_per_gas();

        if fee_cap < self.config.minimal_protocol_basefee as u128 {
            return Err(InsertErr::FeeCapBelowMinimumProtocolFeeCap { fee_cap });
        }
        if fee_cap >= self.config.pending_base_fee as u128 {
            state.insert(TxState::ENOUGH_FEE_CAP_BLOCK);
        }

        Ok(state)
    }

    /// Creates a pool internal transaction
    fn create_pool_tx(
        &self,
        transaction: Arc<TxEnvelope>,
        state: TxState,
    ) -> PoolInternalTransaction {
        PoolInternalTransaction {
            transaction,
            subpool: state.into(),
            state,
            cumulative_cost: U256::ZERO,
        }
    }

    /// Inserts a transaction into the pool or replaces an existing transaction with the same nonce
    fn insert_or_replace_tx(
        &mut self,
        transaction_id: TransactionId,
        pool_tx: PoolInternalTransaction,
    ) -> Result<Option<(Arc<TxEnvelope>, SubPool)>, InsertErr> {
        match self.all_transactions.txs.entry(transaction_id) {
            Entry::Vacant(entry) => {
                // Insert the transaction in both maps
                self.all_transactions
                    .by_hash
                    .insert(*pool_tx.transaction.tx_hash(), pool_tx.transaction.clone());
                entry.insert(pool_tx);
                Ok(None)
            }
            Entry::Occupied(mut entry) => {
                // Transaction with the same nonce already exists: replacement candidate
                let existing_transaction = entry.get().transaction.as_ref();

                // Get the Signed<TxEip1559> type for existing transaction
                let signed_existing_tx_ref = match existing_transaction {
                    TxEnvelope::Eip1559(signed_tx) => signed_tx,
                    _ => return Err(InsertErr::UnknownTransactionType),
                };

                // Get the TxEip1559 type for existing transaction
                let unsigned_existing_tx_ref = signed_existing_tx_ref.tx();

                let existing_max_fee_per_gas = unsigned_existing_tx_ref.max_fee_per_gas;

                // Ensure the new transaction is not underpriced
                if Self::is_underpriced(
                    existing_max_fee_per_gas,
                    pool_tx.transaction.max_fee_per_gas(),
                ) {
                    return Err(InsertErr::Underpriced {
                        existing: *existing_transaction.tx_hash(),
                    });
                }

                // Replace the existing transaction with the new transaction
                let new_hash = *pool_tx.transaction.tx_hash();
                let new_transaction = pool_tx.transaction.clone();
                let replaced = entry.insert(pool_tx);
                self.all_transactions
                    .by_hash
                    .remove(replaced.transaction.tx_hash());
                self.all_transactions
                    .by_hash
                    .insert(new_hash, new_transaction);

                Ok(Some((replaced.transaction, replaced.subpool)))
            }
        }
    }

    /// Updates the descendant transactions
    fn update_descendant_transactions(
        &mut self,
        transaction_id: TransactionId,
        on_chain_balance: U256,
        on_chain_nonce: u64,
        tx_nonce: u64,
        signer: Address,
        pool_tx: PoolInternalTransaction,
        replaced_tx: Option<(Arc<TxEnvelope>, SubPool)>,
    ) -> InsertResult {
        let mut state = TxState::default();
        let mut cumulative_cost = U256::ZERO;
        let mut updates = Vec::new();

        let on_chain_id = TransactionId::new(signer, on_chain_nonce);

        {
            // get all transactions of the sender's account
            let mut descendants = self
                .all_transactions
                .descendant_txs_mut(&on_chain_id)
                .peekable();

            // Tracks the next nonce we expect if the transactions are gapless
            let mut next_nonce = on_chain_id.nonce;

            let ancestor = TransactionId::ancestor(tx_nonce, on_chain_nonce, signer);
            let mut has_parked_ancestor = if ancestor.is_none() {
                false
            } else {
                let (id, tx) = descendants.peek().expect("includes >= 1");
                if id.nonce < tx_nonce {
                    // Looking at a transaction that comes before our new transaction. In this case, we check if that earlier transaction is NOT pending. This helps determine if there are any queued transactions that need to be processed first.
                    !tx.state.is_pending()
                } else {
                    // If id.nonce >= tx_nonce: We return true to indicate there is a queued ancestor, since we've found a transaction with a higher or equal nonce that comes before our current transaction in processing order.
                    true
                }
            };

            // Traverse all transactions of the sender and update existing transactions
            for (id, tx) in descendants {
                let current_pool = tx.subpool;

                // If there's a nonce gap, we can shortcircuit
                if next_nonce != id.nonce {
                    break;
                }

                // close the nonce gap
                tx.state.insert(TxState::NO_NONCE_GAPS);

                // set cumulative cost
                tx.cumulative_cost = cumulative_cost;

                // Update for next transaction
                cumulative_cost = tx.next_cumulative_cost();

                if cumulative_cost > on_chain_balance {
                    // sender lacks sufficient funds to pay for this transaction
                    tx.state.remove(TxState::ENOUGH_BALANCE);
                } else {
                    tx.state.insert(TxState::ENOUGH_BALANCE);
                }

                // Update ancestor condition.
                if has_parked_ancestor {
                    tx.state.remove(TxState::NO_PARKED_ANCESTORS);
                } else {
                    tx.state.insert(TxState::NO_PARKED_ANCESTORS);
                }
                // Update for next iteration
                has_parked_ancestor = !tx.state.is_pending();

                // update the pool based on the state
                tx.subpool = tx.state.into();

                if transaction_id.eq(id) {
                    // if it is the new transaction, track its updated state
                    state = tx.state;
                } else {
                    // check if anything changed
                    if current_pool != tx.subpool {
                        updates.push(PoolUpdate {
                            id: *id,
                            hash: *tx.transaction.tx_hash(),
                            current: current_pool,
                            destination: Destination::Pool(tx.subpool),
                        })
                    }
                }

                // increment for next iteration
                next_nonce = id.next_nonce();
            }
        }

        // If this wasn't a replacement transaction we need to update the counter.
        if replaced_tx.is_none() {
            self.all_transactions.tx_inc(transaction_id.sender);
        }

        Ok(InsertOk {
            transaction: pool_tx.transaction.clone(),
            move_to: state.into(),
            state,
            replaced_tx,
            updates,
        })
    }

    /// Validation checks for new transaction
    ///
    /// Enforces additional rules:
    /// - Spam protection: reject transactions from senders that have exhausted their slot capacity
    /// - Gas limit: reject transactions that exceed a block's maximum gas
    fn ensure_valid(
        &self,
        transaction: Arc<TxEnvelope>, // Take an Arc by value
        tx_gas_limit: u64,
        signer: &Address,
        on_chain_nonce: u64,
        tx_nonce: u64,
    ) -> Result<Arc<TxEnvelope>, InsertErr> {
        // Get the number of transactions sent by the sender
        let user_tx_count = self
            .all_transactions
            .tx_counter
            .get(signer)
            .copied()
            .unwrap_or_default();

        // Check if the sender has exceeded the maximum number of transactions allowed
        if user_tx_count >= self.config.max_account_slots {
            return Err(InsertErr::ExceededSenderTransactionsCapacity {
                address: *signer,
            });
        }

        // Check if the transaction gas limit exceeds the block gas limit
        if tx_gas_limit > self.config.block_gas_limit {
            return Err(InsertErr::TxGasLimitMoreThanAvailableBlockGas {
                block_gas_limit: self.config.block_gas_limit,
                tx_gas_limit,
            });
        }

        // Check if the transaction nonce is greater than the on-chain nonce
        if on_chain_nonce > tx_nonce {
            return Err(InsertErr::InvalidTxNonce {
                on_chain_nonce,
                tx_nonce,
            });
        }

        Ok(transaction)
    }

    /// Checks if the new transaction is underpriced
    fn is_underpriced(
        existing_max_fee_per_gas: u128,
        possible_replacement_max_fee_per_gas: u128,
    ) -> bool {
        possible_replacement_max_fee_per_gas < existing_max_fee_per_gas
    }

    /// Inserts the transaction into the given sub-pool.
    /// Optionally, removes the replacement transaction.
    fn add_new_transaction(
        &mut self,
        transaction: Arc<TxEnvelope>,
        replaced: Option<(Arc<TxEnvelope>, SubPool)>,
        pool: SubPool,
    ) {
        if let Some((replaced, replaced_pool)) = replaced {
            // Remove the replaced transaction
            self.remove_from_subpool(replaced_pool, &replaced.into());
        }

        self.add_transaction_to_subpool(pool, transaction)
    }

    /// Removes the transaction from the given pool.
    ///
    /// Caution: this only removes the tx from the sub-pool and not from the pool itself
    fn remove_from_subpool(
        &mut self,
        pool: SubPool,
        tx: &TransactionId,
    ) -> Option<Arc<TxEnvelope>> {
        match pool {
            SubPool::Queued => self.queued_transactions.remove_transaction(tx),
            SubPool::Pending => self.pending_transactions.remove_transaction(tx),
        }
    }

    /// Inserts the transaction into the given sub-pool.
    fn add_transaction_to_subpool(&mut self, pool: SubPool, tx: Arc<TxEnvelope>) {
        match pool {
            SubPool::Queued => self.queued_transactions.add_transaction(tx),
            SubPool::Pending => {
                self.pending_transactions
                    .add_transaction(tx, self.config.pending_base_fee);
            }
        }
    }

    /// Maintenance task to apply a series of updates.
    ///
    /// This will move/discard the given transaction according to the `PoolUpdate`
    fn process_updates(&mut self, updates: Vec<PoolUpdate>) -> UpdateOutcome {
        let mut outcome = UpdateOutcome::default();
        for PoolUpdate {
            id,
            hash,
            current,
            destination,
        } in updates
        {
            match destination {
                Destination::Discard => {
                    // remove the transaction from the pool and subpool
                    if let Some(tx) = self.prune_transaction_by_hash(&hash) {
                        outcome.discarded.push(tx);
                    }
                }
                Destination::Pool(move_to) => {
                    debug_assert_ne!(&move_to, &current, "destination must be different");
                    let moved = self.move_transaction(current, move_to, &id);
                    if matches!(move_to, SubPool::Pending) {
                        if let Some(tx) = moved {
                            outcome.promoted.push(tx);
                        }
                    }
                }
            }
        }
        outcome
    }

    /// This removes the transaction from the pool and advances any descendant state inside the
    /// subpool.
    ///
    /// This is intended to be used when a transaction is included in a block,
    fn prune_transaction_by_hash(&mut self, tx_hash: &B256) -> Option<Arc<TxEnvelope>> {
        let (tx, pool) = self.all_transactions.remove_transaction_by_hash(tx_hash)?;

        self.remove_from_subpool(pool, &tx.into())
    }

    /// Moves a transaction from one sub pool to another.
    ///
    /// This will remove the given transaction from one sub-pool and insert it into the other
    /// sub-pool.
    fn move_transaction(
        &mut self,
        from: SubPool,
        to: SubPool,
        id: &TransactionId,
    ) -> Option<Arc<TxEnvelope>> {
        let tx = self.remove_from_subpool(from, id)?;
        self.add_transaction_to_subpool(to, tx.clone());
        Some(tx)
    }

    /// Converts an insert error to a pool error
    fn convert_insert_error(&self, err: InsertErr, tx_hash: B256) -> PoolError {
        let kind = match err {
            InsertErr::UnknownTransactionType => PoolErrorKind::UnknownTransactionType,
            InsertErr::InvalidTxNonce { on_chain_nonce, tx_nonce } => 
                PoolErrorKind::InvalidTxNonce(on_chain_nonce, tx_nonce),
            InsertErr::SignatureError => PoolErrorKind::SignatureError,
            InsertErr::Underpriced { existing } => 
                PoolErrorKind::ReplacementUnderpriced(existing),
            InsertErr::FeeCapBelowMinimumProtocolFeeCap { fee_cap } => 
                PoolErrorKind::FeeCapBelowMinimumProtocolFeeCap(fee_cap),
            InsertErr::ExceededSenderTransactionsCapacity { address } => 
                PoolErrorKind::SpammerExceededCapacity(address),
            InsertErr::TxGasLimitMoreThanAvailableBlockGas { block_gas_limit, tx_gas_limit } => 
                PoolErrorKind::TxGasLimitMoreThanAvailableBlockGas(block_gas_limit, tx_gas_limit),
        };
        PoolError::new(tx_hash, kind)
    }

    /// Processes the result of a successful transaction insertion
    fn process_insert_ok(&mut self, insert_ok: InsertOk) -> PoolResult<AddedTransaction> {
        let InsertOk {
            transaction,
            move_to,
            replaced_tx,
            updates,
            ..
        } = insert_ok;

        self.add_new_transaction(transaction.clone(), replaced_tx.clone(), move_to);
        let UpdateOutcome { promoted, discarded } = self.process_updates(updates);
        
        let replaced = replaced_tx.map(|(tx, _)| tx);
        
        Ok(if move_to.is_pending() {
            AddedTransaction::Pending(AddedPendingTransaction {
                transaction,
                promoted,
                discarded,
                replaced,
            })
        } else {
            AddedTransaction::Queued {
                transaction,
                subpool: move_to,
                replaced,
            }
        })
    }

    /// Returns the number of transactions in the pool for a given sender
    pub fn get_sender_transaction_count(&self, sender: &Address) -> usize {
        self.all_transactions.tx_counter.get(sender).copied().unwrap_or_default()
    }

    /// Returns true if the sender has reached their transaction limit
    pub fn is_sender_at_capacity(&self, sender: &Address) -> bool {
        self.get_sender_transaction_count(sender) >= self.config.max_account_slots
    }

    /// Checks if a transaction's gas price meets minimum requirements
    pub fn meets_minimum_gas_price(&self, fee_cap: u128) -> bool {
        fee_cap >= self.config.minimal_protocol_basefee as u128
    }
}

/// The internal transaction typed used by `Pool` which contains additional info used for
/// determining the current state of the transaction.
#[derive(Debug, Clone)]
pub(crate) struct PoolInternalTransaction {
    /// The actual transaction object.
    pub(crate) transaction: Arc<TxEnvelope>,
    /// The `SubPool` that currently contains this transaction.
    pub(crate) subpool: SubPool,
    /// Keeps track of the current state of the transaction and therefore in which subpool it
    /// should reside
    pub(crate) state: TxState,
    /// The total cost of all transactions before this transaction.
    ///
    /// This is the combined `cost` of all transactions from the same sender that currently
    /// come before this transaction.
    pub(crate) cumulative_cost: U256,
}

impl PoolInternalTransaction {
    /// Returns the transaction
    #[allow(dead_code)]
    fn transaction(&self) -> Arc<TxEnvelope> {
        self.transaction.clone()
    }

    /// Used to sum the cost of all transactions to update PoolInternalTransaction.cumulative_cost
    fn next_cumulative_cost(&self) -> U256 {
        self.cumulative_cost + self.cost()
    }

    /// Returns the cost that this transaction is allowed to consume:
    ///
    /// For EIP-1559 transactions: `max_fee_per_gas * gas_limit + tx_value`.
    fn cost(&self) -> U256 {
        // System currently only handles Eip1559 txs
        let signed_tx = self
            .transaction
            .as_eip1559()
            .expect("Unknown transaction type");
        let unsigned_tx = signed_tx.tx();

        let max_fee_per_gas = unsigned_tx.max_fee_per_gas;
        let gas_limit = unsigned_tx.gas_limit;
        let value = unsigned_tx.value;

        U256::from(max_fee_per_gas) * U256::from(gas_limit) + value
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use alloy::primitives::U256;
    use crate::ordering::CoinbaseTipOrdering;
    use crate::pool::PoolConfig;
    use crate::result::{AddedTransaction, PoolErrorKind, };
    use crate::test_utils::helpers::{
        create_default_tx_and_sender, create_default_tx_envelope_and_sender,
        create_pool_internal_tx, create_pool_internal_tx_with_cumulative_cost, create_sender,
         create_tx_and_sender, create_tx_envelope_with_sender,
    };

    fn create_test_pool() -> Pool<CoinbaseTipOrdering<TxEnvelope>> {
        create_test_pool_with_config(PoolConfig {
            max_account_slots: 16,
            block_gas_limit: 30_000_000,
            minimal_protocol_basefee: 5,
            pending_base_fee: 10,
        })
    }

    fn create_test_pool_with_config(config: PoolConfig) -> Pool<CoinbaseTipOrdering<TxEnvelope>> {
        let ordering: CoinbaseTipOrdering<TxEnvelope> = CoinbaseTipOrdering::default();

        Pool::new(config, ordering)
    }

    #[tokio::test]
    async fn test_pool_internal_transaction_cumulative_cost() {
        let (tx, _, _) = create_default_tx_and_sender().await;
        let pool_internal_tx = create_pool_internal_tx(Arc::clone(&tx));

        // Calculate expected cost
        let signed_tx = tx.as_eip1559().expect("Should be EIP-1559 transaction");
        let unsigned_tx = signed_tx.tx();
        let expected_cost = U256::from(unsigned_tx.max_fee_per_gas)
            * U256::from(unsigned_tx.gas_limit)
            + unsigned_tx.value;

        // Test cost calculation
        assert_eq!(pool_internal_tx.cost(), expected_cost);

        // Test next_cumulative_cost with zero initial cumulative_cost
        assert_eq!(pool_internal_tx.next_cumulative_cost(), expected_cost);

        // Test with non-zero cumulative_cost
        let initial_cumulative_cost = U256::from(1_000_000);
        let pool_internal_tx_with_cumulative =
            create_pool_internal_tx_with_cumulative_cost(Arc::clone(&tx), initial_cumulative_cost);

        assert_eq!(
            pool_internal_tx_with_cumulative.next_cumulative_cost(),
            expected_cost + initial_cumulative_cost
        );
    }

    #[tokio::test]
    async fn test_pool_internal_transaction_with_different_gas_values() {
        let (tx1, _, _) = create_tx_and_sender(20, 10, 100000, U256::ZERO, 0).await;
        let (tx2, _, _) = create_tx_and_sender(30, 15, 150000, U256::from(1000), 1).await;

        let pool_internal_tx1 = create_pool_internal_tx(Arc::clone(&tx1));
        let pool_internal_tx2 = create_pool_internal_tx(Arc::clone(&tx2));

        assert!(pool_internal_tx2.cost() > pool_internal_tx1.cost());
    }

    #[tokio::test]
    async fn test_add_transaction() {
        let mut pool = create_test_pool();

        let (tx, _, _) = create_default_tx_envelope_and_sender().await;
        let on_chain_balance = U256::from(1_000_000);
        let on_chain_nonce = 0;

        let result = pool.add_transaction(tx.clone(), on_chain_balance, on_chain_nonce);

        let tx_arc = Arc::new(tx.clone());

        assert!(result.is_ok());
        if let Ok(AddedTransaction::Pending(added_tx)) = result {
            assert_eq!(added_tx.transaction.clone(), tx_arc.clone());
            assert!(added_tx.promoted.is_empty());
            assert!(added_tx.discarded.is_empty());
            assert!(added_tx.replaced.is_none());
        } else {
            panic!("Expected Pending transaction");
        }

        assert!(pool.all_transactions.contains(tx.tx_hash()));
        assert!(pool
            .pending_transactions
            .contains(&TransactionId::from(tx_arc.clone())));
        assert!(!pool
            .queued_transactions
            .contains(&TransactionId::from(tx_arc.clone())));
    }

    #[tokio::test]
    async fn test_add_transaction_to_promote_descendants_to_pending() {
        // Create a pool
        let mut pool = create_test_pool();
        let (sender, private_key) = create_sender();
        let on_chain_balance = U256::from(1_000_000_000);
        let on_chain_nonce = 0;

        // Create and add three transactions with consecutive nonces starting from on_chain_nonce + 1
        let mut tx_ids = vec![];
        for i in 1..=3 {
            let tx = create_tx_envelope_with_sender(
                private_key.clone(),
                sender,
                20,
                10,
                100_000,
                U256::ZERO,
                on_chain_nonce + i,
            )
            .await;
            let result = pool.add_transaction(tx.clone(), on_chain_balance, on_chain_nonce);
            assert!(result.is_ok());
            tx_ids.push(TransactionId::from(Arc::new(tx.clone())));
        }

        // Verify that all transaction are in queued, because the nonces start from on_chain_nonce + 1
        assert!(pool.queued_transactions.contains(&tx_ids[0]));
        assert!(pool.queued_transactions.contains(&tx_ids[1]));
        assert!(pool.queued_transactions.contains(&tx_ids[2]));

        // Create a new transaction with nonce equal to on_chain_nonce
        let new_tx = create_tx_envelope_with_sender(
            private_key,
            sender,
            30, // Higher fee to replace the existing transaction
            15,
            100_000,
            U256::ZERO,
            on_chain_nonce,
        )
        .await;

        // Add the new transaction
        let result = pool.add_transaction(new_tx.clone(), on_chain_balance, on_chain_nonce);
        assert!(result.is_ok());

        // Adding the transaction should move it to pending and promote the other transactions to pending
        if let Ok(AddedTransaction::Pending(added_tx)) = result {
            // Check that the new transaction replaced the old one
            assert!(added_tx.replaced.is_none());

            // Check that the other transactions were promoted
            assert_eq!(added_tx.promoted.len(), 3);

            // Verify final state of the pool
            assert!(pool.pending_transactions.contains(&tx_ids[0]));
            assert!(pool.pending_transactions.contains(&tx_ids[1]));
            assert!(pool.pending_transactions.contains(&tx_ids[2]));

            // Verify that the added transaction is in the pending pool
            assert!(pool
                .pending_transactions
                .contains(&TransactionId::from(Arc::new(new_tx.clone()))));

            // Verify that the new transaction is in the pool
            assert!(pool.contains(new_tx.tx_hash()));
        } else {
            panic!("Expected Pending transaction");
        }
    }

    #[tokio::test]
    async fn test_add_transaction_already_imported() {
        let mut pool = create_test_pool();

        let (tx, sender, _) = create_default_tx_envelope_and_sender().await;
        let on_chain_balance = U256::from(1_000_000);
        let on_chain_nonce = 0;

        // Add transaction for the first time
        let result = pool.add_transaction(tx.clone(), on_chain_balance, on_chain_nonce);
        assert!(result.is_ok());

        // Try to add the same transaction again
        let result = pool.add_transaction(tx.clone(), on_chain_balance, on_chain_nonce);

        assert!(result.is_err());
        if let Err(error) = result {
            assert_eq!(error.kind, PoolErrorKind::AlreadyImported);
        }

        // Verify that the transaction is in the pool only once
        assert_eq!(
            pool.all_transactions.tx_counter.get(&sender).unwrap_or(&0),
            &1usize
        );
        assert!(pool.contains(tx.tx_hash()));
    }

    #[tokio::test]
    async fn test_add_transaction_with_low_nonce() {
        let mut pool = create_test_pool();

        let (tx, _, _) = create_default_tx_envelope_and_sender().await;
        let on_chain_balance = U256::from(1_000_000);
        let on_chain_nonce = 5; // Set on-chain nonce higher than the transaction's nonce

        // Attempt to add transaction with a nonce lower than on-chain nonce
        let result = pool.add_transaction(tx.clone(), on_chain_balance, on_chain_nonce);

        assert!(result.is_err());
        if let Err(error) = result {
            assert_eq!(error.kind, PoolErrorKind::InvalidTxNonce(on_chain_nonce, 0));
        }

        // Verify that the transaction is not in the pool
        let tx_arc = Arc::new(tx.clone());
        assert!(!pool.contains(tx.tx_hash()));
        assert!(pool.all_transactions.tx_counter.is_empty());
        assert!(!pool
            .pending_transactions
            .contains(&TransactionId::from(tx_arc.clone())));
        assert!(!pool
            .queued_transactions
            .contains(&TransactionId::from(tx_arc.clone())));
    }

    #[tokio::test]
    async fn test_add_transaction_replacement_underpriced() {
        let mut pool = create_test_pool();

        let (tx1, sender, private_key) = create_default_tx_envelope_and_sender().await;
        let on_chain_balance = U256::from(1_000_000);
        let on_chain_nonce = 0;

        // Add the first transaction
        let result = pool.add_transaction(tx1.clone(), on_chain_balance, on_chain_nonce);
        assert!(result.is_ok());

        // Create a replacement transaction with the same nonce but lower gas price
        let tx2 =
            create_tx_envelope_with_sender(private_key, sender, 5, 5, 100000, U256::ZERO, 0).await;

        // Try to add the replacement transaction
        let result = pool.add_transaction(tx2.clone(), on_chain_balance, on_chain_nonce);

        assert!(result.is_err());
        if let Err(error) = result {
            assert!(matches!(
                error.kind,
                PoolErrorKind::ReplacementUnderpriced(_)
            ));
            if let PoolErrorKind::ReplacementUnderpriced(existing_tx_hash) = error.kind {
                assert_eq!(existing_tx_hash, *tx1.tx_hash());
            }
        }

        // Verify that the original transaction is still in the pool
        assert!(pool.contains(tx1.tx_hash()));
        assert!(!pool.contains(tx2.tx_hash()));
        assert_eq!(
            pool.all_transactions.tx_counter.get(&sender).unwrap_or(&0),
            &1usize
        );
    }

    #[tokio::test]
    async fn test_add_transaction_fee_cap_below_minimum_protocol_fee_cap() {
        let mut pool = create_test_pool();
        let (sender, private_key) = create_sender();

        // Create a transaction with fee cap below the minimum protocol fee cap
        let tx = create_tx_envelope_with_sender(
            private_key,
            sender,
            4, // max_fee_per_gas set below minimal_protocol_basefee (5)
            4, // max_priority_fee_per_gas
            100000,
            U256::ZERO,
            0,
        )
        .await;

        let on_chain_balance = U256::from(1_000_000);
        let on_chain_nonce = 0;

        // Attempt to add the transaction
        let result = pool.add_transaction(tx.clone(), on_chain_balance, on_chain_nonce);

        // Assert that the result is an error
        assert!(result.is_err());
        if let Err(error) = result {
            assert!(matches!(
                error.kind,
                PoolErrorKind::FeeCapBelowMinimumProtocolFeeCap(4)
            ));
        }

        // Verify that the transaction is not in the pool
        assert!(!pool.contains(tx.tx_hash()));
        assert!(pool.all_transactions.tx_counter.is_empty());
        assert!(!pool
            .pending_transactions
            .contains(&TransactionId::from(Arc::new(tx.clone()))));
        assert!(!pool
            .queued_transactions
            .contains(&TransactionId::from(Arc::new(tx.clone()))));
    }

    #[tokio::test]
    async fn test_add_transaction_spammer_exceeded_capacity() {
        let mut pool = create_test_pool();
        let (sender, private_key) = create_sender();
        let on_chain_balance = U256::from(1_000_000_000); // Large balance to avoid insufficient funds
        let on_chain_nonce = 0;

        // Add transactions up to the max_account_slots limit
        for i in 0..pool.config.max_account_slots {
            let tx = create_tx_envelope_with_sender(
                private_key.clone(),
                sender,
                20, // max_fee_per_gas
                10, // max_priority_fee_per_gas
                100000,
                U256::ZERO,
                i as u64,
            )
            .await;

            let result = pool.add_transaction(tx, on_chain_balance, on_chain_nonce);
            assert!(result.is_ok());
        }

        // Attempt to add one more transaction, which should exceed the capacity
        let excess_tx = create_tx_envelope_with_sender(
            private_key,
            sender,
            20,
            10,
            100000,
            U256::ZERO,
            pool.config.max_account_slots as u64,
        )
        .await;

        let result = pool.add_transaction(excess_tx.clone(), on_chain_balance, on_chain_nonce);

        // Assert that the result is an error
        assert!(result.is_err());
        if let Err(error) = result {
            assert!(
                matches!(error.kind, PoolErrorKind::SpammerExceededCapacity(addr) if addr == sender)
            );
        }

        // Verify that the excess transaction is not in the pool
        assert!(!pool.contains(excess_tx.tx_hash()));
        assert_eq!(
            pool.all_transactions.tx_counter.get(&sender).unwrap_or(&0),
            &pool.config.max_account_slots
        );
    }

    #[tokio::test]
    async fn test_add_transaction_gas_limit_exceeds_block_gas() {
        let mut pool = create_test_pool();
        let (sender, private_key) = create_sender();
        let on_chain_balance = U256::from(1_000_000_000); // Large balance to avoid insufficient funds
        let on_chain_nonce = 0;

        // Create a transaction with gas limit higher than the block gas limit
        let tx = create_tx_envelope_with_sender(
            private_key,
            sender,
            20,                              // max_fee_per_gas
            10,                              // max_priority_fee_per_gas
            pool.config.block_gas_limit + 1, // Exceeds block gas limit
            U256::ZERO,
            on_chain_nonce,
        )
        .await;

        let result = pool.add_transaction(tx.clone(), on_chain_balance, on_chain_nonce);

        // Assert that the result is an error
        assert!(result.is_err());
        if let Err(error) = result {
            assert!(matches!(
                error.kind,
                PoolErrorKind::TxGasLimitMoreThanAvailableBlockGas(block_gas, tx_gas)
                if block_gas == pool.config.block_gas_limit && tx_gas == pool.config.block_gas_limit + 1
            ));
        }

        // Verify that the transaction is not in the pool
        assert!(!pool.contains(tx.tx_hash()));
        assert_eq!(
            pool.all_transactions.tx_counter.get(&sender).unwrap_or(&0),
            &0
        );
    }

    #[tokio::test]
    async fn test_ensure_valid_success() {
        let pool = create_test_pool();
        let (sender, private_key) = create_sender();
        let on_chain_nonce = 0;

        let tx = create_tx_envelope_with_sender(
            private_key,
            sender,
            20,
            10,
            100_000,
            U256::ZERO,
            on_chain_nonce,
        )
        .await;

        let result = pool.ensure_valid(
            Arc::new(tx),
            100_000,
            &sender,
            on_chain_nonce,
            on_chain_nonce,
        );
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_ensure_valid_exceeded_sender_transactions_capacity() {
        let mut pool = create_test_pool();
        let (sender, private_key) = create_sender();
        let on_chain_nonce = 0;

        // Fill up the pool to max capacity
        for _ in 0..pool.config.max_account_slots {
            pool.all_transactions.tx_inc(sender);
        }

        // Try to add one more transaction
        let excess_tx = create_tx_envelope_with_sender(
            private_key.clone(),
            sender,
            20,
            10,
            100_000,
            U256::ZERO,
            on_chain_nonce + pool.config.max_account_slots as u64,
        )
        .await;

        let result = pool.ensure_valid(
            Arc::new(excess_tx),
            100_000,
            &sender,
            on_chain_nonce,
            on_chain_nonce + pool.config.max_account_slots as u64,
        );
        assert!(
            matches!(result, Err(InsertErr::ExceededSenderTransactionsCapacity { address }) if address == sender)
        );
    }

    #[tokio::test]
    async fn test_ensure_valid_tx_gas_limit_more_than_available_block_gas() {
        let pool = create_test_pool();
        let (sender, private_key) = create_sender();
        let on_chain_nonce = 0;

        let tx = create_tx_envelope_with_sender(
            private_key,
            sender,
            20,
            10,
            pool.config.block_gas_limit + 1,
            U256::ZERO,
            on_chain_nonce,
        )
        .await;

        let result = pool.ensure_valid(
            Arc::new(tx),
            pool.config.block_gas_limit + 1,
            &sender,
            on_chain_nonce,
            on_chain_nonce,
        );
        assert!(
            matches!(result, Err(InsertErr::TxGasLimitMoreThanAvailableBlockGas { block_gas_limit, tx_gas_limit })
            if block_gas_limit == pool.config.block_gas_limit && tx_gas_limit == pool.config.block_gas_limit + 1)
        );
    }

    #[tokio::test]
    async fn test_ensure_valid_invalid_tx_nonce() {
        let pool = create_test_pool();
        let (sender, private_key) = create_sender();
        let on_chain_nonce = 5;

        let tx = create_tx_envelope_with_sender(
            private_key,
            sender,
            20,
            10,
            100_000,
            U256::ZERO,
            on_chain_nonce - 1,
        )
        .await;

        let result = pool.ensure_valid(
            Arc::new(tx),
            100_000,
            &sender,
            on_chain_nonce,
            on_chain_nonce - 1,
        );
        assert!(
            matches!(result, Err(InsertErr::InvalidTxNonce { on_chain_nonce: chain_nonce, tx_nonce })
            if chain_nonce == on_chain_nonce && tx_nonce == on_chain_nonce - 1)
        );
    }

    #[test]
    fn test_is_underpriced() {
        // Test case where the replacement transaction is underpriced
        assert!(Pool::<CoinbaseTipOrdering<TxEnvelope>>::is_underpriced(
            100, 99
        ));
        assert!(Pool::<CoinbaseTipOrdering<TxEnvelope>>::is_underpriced(
            1000, 999
        ));

        // Test case where the replacement transaction is not underpriced (equal price)
        assert!(!Pool::<CoinbaseTipOrdering<TxEnvelope>>::is_underpriced(
            100, 100
        ));

        // Test case where the replacement transaction is not underpriced (higher price)
        assert!(!Pool::<CoinbaseTipOrdering<TxEnvelope>>::is_underpriced(
            100, 101
        ));
        assert!(!Pool::<CoinbaseTipOrdering<TxEnvelope>>::is_underpriced(
            1000, 1001
        ));

        // Test edge cases
        assert!(Pool::<CoinbaseTipOrdering<TxEnvelope>>::is_underpriced(
            1, 0
        ));
        assert!(!Pool::<CoinbaseTipOrdering<TxEnvelope>>::is_underpriced(
            0, 0
        ));
        assert!(!Pool::<CoinbaseTipOrdering<TxEnvelope>>::is_underpriced(
            0, 1
        ));

        // Test with maximum u128 values
        assert!(!Pool::<CoinbaseTipOrdering<TxEnvelope>>::is_underpriced(
            u128::MAX - 1,
            u128::MAX
        ));
        assert!(Pool::<CoinbaseTipOrdering<TxEnvelope>>::is_underpriced(
            u128::MAX,
            u128::MAX - 1
        ));
    }

    #[tokio::test]
    async fn test_transaction_sequence_same_sender() {
        // Tests the ordering of transactions in the pool. We expect transactions from the same sender to come out in order of nonce.
        let mut pool = create_test_pool();
        let (sender, private_key) = create_sender();
        let on_chain_balance = U256::from(1_000_000_000);
        let on_chain_nonce = 0;

        // Create transactions with different nonces and priority fees
        let tx1 = create_tx_envelope_with_sender(
            private_key.clone(),
            sender,
            20,
            10,
            100_000,
            U256::ZERO,
            2,
        )
        .await;
        let tx2 = create_tx_envelope_with_sender(
            private_key.clone(),
            sender,
            25,
            15,
            100_000,
            U256::ZERO,
            1,
        )
        .await;
        let tx3 = create_tx_envelope_with_sender(
            private_key.clone(),
            sender,
            15,
            5,
            100_000,
            U256::ZERO,
            0,
        )
        .await;
        let tx4 = create_tx_envelope_with_sender(
            private_key.clone(),
            sender,
            30,
            20,
            100_000,
            U256::ZERO,
            3,
        )
        .await;

        // Add transactions to the pool in a mixed order
        pool.add_transaction(tx2.clone(), on_chain_balance, on_chain_nonce)
            .unwrap();
        pool.add_transaction(tx4.clone(), on_chain_balance, on_chain_nonce)
            .unwrap();
        pool.add_transaction(tx1.clone(), on_chain_balance, on_chain_nonce)
            .unwrap();
        pool.add_transaction(tx3.clone(), on_chain_balance, on_chain_nonce)
            .unwrap();

        // Create transaction sequence
        let mut sequence = pool.transaction_sequence();

        // Check that transactions come out in the correct order (by nonce)
        assert_eq!(
            sequence.next().unwrap().transaction().tx_hash(),
            tx3.tx_hash()
        );
        assert_eq!(
            sequence.next().unwrap().transaction().tx_hash(),
            tx2.tx_hash()
        );
        assert_eq!(
            sequence.next().unwrap().transaction().tx_hash(),
            tx1.tx_hash()
        );
        assert_eq!(
            sequence.next().unwrap().transaction().tx_hash(),
            tx4.tx_hash()
        );
        assert!(sequence.next().is_none());
    }

    #[tokio::test]
    async fn test_transaction_sequence_multiple_senders() {
        // Tests the ordering of transactions in the pool. We expect the transactions with the highest effective tip to be at the end of the sequence, since we pop from the end of the sequence during execution.
        let mut pool = create_test_pool();
        let (sender1, private_key1) = create_sender();
        let (sender2, private_key2) = create_sender();
        let on_chain_balance = U256::from(1_000_000_000);

        // Create transactions for sender1 with different nonces and priority fees
        // private_key, sender , max_fee_per_gas: u128, max_priority_fee_per_gas: u128, gas_limit: u64, value: U256, nonce: u64
        let tx1_1 = create_tx_envelope_with_sender(
            private_key1.clone(),
            sender1,
            20,
            10,
            100_000,
            U256::ZERO,
            0,
        )
        .await;
        let tx1_2 = create_tx_envelope_with_sender(
            private_key1.clone(),
            sender1,
            25,
            15,
            100_000,
            U256::ZERO,
            1,
        )
        .await;
        let tx1_3 = create_tx_envelope_with_sender(
            private_key1.clone(),
            sender1,
            30,
            20,
            100_000,
            U256::ZERO,
            2,
        )
        .await;

        // Create transactions for sender2 with different nonces and priority fees
        let tx2_1 = create_tx_envelope_with_sender(
            private_key2.clone(),
            sender2,
            15,
            5,
            100_000,
            U256::ZERO,
            0,
        )
        .await;
        let tx2_2 = create_tx_envelope_with_sender(
            private_key2.clone(),
            sender2,
            20,
            10,
            100_000,
            U256::ZERO,
            1,
        )
        .await;
        let tx2_3 = create_tx_envelope_with_sender(
            private_key2.clone(),
            sender2,
            35,
            25,
            100_000,
            U256::ZERO,
            2,
        )
        .await;

        // Add transactions to the pool in a mixed order
        pool.add_transaction(tx1_2.clone(), on_chain_balance, 0)
            .unwrap();
        pool.add_transaction(tx2_3.clone(), on_chain_balance, 0)
            .unwrap();
        pool.add_transaction(tx1_1.clone(), on_chain_balance, 0)
            .unwrap();
        pool.add_transaction(tx2_1.clone(), on_chain_balance, 0)
            .unwrap();
        pool.add_transaction(tx1_3.clone(), on_chain_balance, 0)
            .unwrap();
        pool.add_transaction(tx2_2.clone(), on_chain_balance, 0)
            .unwrap();

        // Create transaction sequence
        let mut sequence = pool.transaction_sequence();

        // NOTE: For debugging purposes, uncomment the code below to loop through sequence and print each transaction
        // for i in 0..6 {
        //     let next = sequence.next().unwrap();
        //     let sender = next.sender();

        //     // Avoiding unnecessary allocation, using &str instead of String
        //     let name = if sender == sender1 { "sender1" } else { "sender2" };

        //     // Using match instead of multiple if-else statements
        //     let tx_name = match next.transaction().tx_hash() {
        //         hash if hash == tx1_1.tx_hash() => "tx1_1",
        //         hash if hash == tx1_2.tx_hash() => "tx1_2",
        //         hash if hash == tx1_3.tx_hash() => "tx1_3",
        //         hash if hash == tx2_1.tx_hash() => "tx2_1",
        //         hash if hash == tx2_2.tx_hash() => "tx2_2",
        //         _ => "tx2_3",
        //     };

        //     println!(
        //         "tx_name: {:?}, tx hash of {}th: {:?}, effective tip: {:?}, sender: {:?}",
        //         tx_name, i, next.transaction().tx_hash(), next.priority(), name
        //     );
        // }

        // Check that transactions come out in the correct order (by sender and nonce)
        assert_eq!(
            sequence.next().unwrap().transaction().tx_hash(),
            tx1_1.tx_hash()
        );
        assert_eq!(
            sequence.next().unwrap().transaction().tx_hash(),
            tx1_2.tx_hash()
        );
        assert_eq!(
            sequence.next().unwrap().transaction().tx_hash(),
            tx1_3.tx_hash()
        );
        assert_eq!(
            sequence.next().unwrap().transaction().tx_hash(),
            tx2_1.tx_hash()
        );
        assert_eq!(
            sequence.next().unwrap().transaction().tx_hash(),
            tx2_2.tx_hash()
        );
        assert_eq!(
            sequence.next().unwrap().transaction().tx_hash(),
            tx2_3.tx_hash()
        );
        assert!(sequence.next().is_none());
    }
}
