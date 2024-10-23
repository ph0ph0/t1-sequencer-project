pub mod all;
pub mod pending;
pub mod queued;
pub mod state;
pub mod sequence;

// ------pool.rs-----
use std::collections::btree_map::Entry;
use std::sync::Arc;

use alloy::{
    consensus::{TxEnvelope, Transaction},
    primitives::{Address, B256, U256, aliases::TxHash},
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
        AddedPendingTransaction, AddedTransaction, Destination, InsertErr, InsertOk,
        InsertResult, PoolError, PoolErrorKind, PoolResult, PoolUpdate, UpdateOutcome,
    },
};

// TODO: Add derive and impls
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
    pub pending_base_fee: u64
}

// pub struct PoolMetrics { TODO: Needed?

// }


pub struct Pool<O>
where
    O: TransactionOrdering + PartialEq + Eq + PartialOrd + Ord,
{
    config: PoolConfig,
    /// All transactions in the pool, grouped by sender, ordered by nonce
    all_transactions: AllTransactions,
    ///All transactions that can be executed on the current chain state
    pending_transactions: PendingPool<O>,
    /// Struct that holds transactions ordered by priority fee and respects nonce ordering
    /// Represents the best subset of transaction from pending_transactions
    transaction_sequence: TransactionSequence<O>, // TODO: Do we need this?
    /// All transactions that cannot be executed on current state but might be able to in the future
    queued_transactions: QueuedPool,
    // Metrics for the pool and subpool
    // metrics: PoolMetrics TODO: Needed?
}

impl<O> Pool<O> 
where
    O: TransactionOrdering + PartialEq + Eq + PartialOrd + Ord,
{
    pub(crate) fn add_transaction(
        &mut self,
        tx: TxEnvelope,
        on_chain_balance: U256,
        on_chain_nonce: u64
    ) -> PoolResult<AddedTransaction>{

        let tx_hash = tx.tx_hash().clone();
        // Check to see if the new tx already exists in the pool
        if self.contains(&tx_hash) {
            return Err(PoolError::new(
                tx_hash.clone(), 
                PoolErrorKind::AlreadyImported))
        }

        // TODO: Update user info?


        match self.insert_tx(tx, on_chain_balance, on_chain_nonce) {
            Ok(InsertOk {transaction, move_to, replaced_tx, updates, ..}) => {
                // replace the new tx and remove the replaced in the subpool(s)
                self.add_new_transaction(transaction.clone(), replaced_tx.clone(), move_to);
                // Update inserted transactions metric
                let UpdateOutcome { promoted, discarded } = self.process_updates(updates);

                let replaced = replaced_tx.map(|(tx, _)| tx);

                // This transaction was moved to the pending pool.
                let res = if move_to.is_pending() {
                    AddedTransaction::Pending(AddedPendingTransaction {
                        transaction,
                        promoted,
                        discarded,
                        replaced,
                    })
                } else {
                    AddedTransaction::Queued { transaction, subpool: move_to, replaced }
                };

                return Ok(res);
            }
            Err(err) => {
                match err {
                    InsertErr::UnknownTransactionType => {
                        return Err(PoolError::new(
                            tx_hash.clone(),
                            PoolErrorKind::UnknownTransactionType,
                        ));
                    },
                    InsertErr::InvalidTxNonce { on_chain_nonce, tx_nonce } => {
                        return Err(PoolError::new(
                            tx_hash.clone(),
                            PoolErrorKind::InvalidTxNonce(on_chain_nonce, tx_nonce),
                        ));
                    },
                    InsertErr::SignatureError => {
                        return Err(PoolError::new(
                            tx_hash.clone(),
                            PoolErrorKind::SignatureError,
                        ));
                    },
                    InsertErr::Underpriced { existing } => {
                        return Err(PoolError::new(
                            tx_hash.clone(),
                            PoolErrorKind::ReplacementUnderpriced(existing),
                        ));
                    },
                    InsertErr::FeeCapBelowMinimumProtocolFeeCap { fee_cap } => {
                        return Err(PoolError::new(
                            tx_hash.clone(),
                            PoolErrorKind::FeeCapBelowMinimumProtocolFeeCap(fee_cap),
                        ));
                    }
                    InsertErr::ExceededSenderTransactionsCapacity { address } => {
                        return Err(PoolError::new(
                            tx_hash.clone(),
                            PoolErrorKind::SpammerExceededCapacity(address),
                        ));
                    }
                    InsertErr::TxGasLimitMoreThanAvailableBlockGas {
                        block_gas_limit,
                        tx_gas_limit,
                    } => {
                        return Err(PoolError::new(
                            tx_hash.clone(),
                            PoolErrorKind::TxGasLimitMoreThanAvailableBlockGas(
                                block_gas_limit,
                                tx_gas_limit,
                            )
                        ));
                    }
                }
            }
        }
    }

    /// Checks if the given tx_hash is present in the all_transactions pool
    pub(crate) fn contains(&self, tx_hash: &TxHash) -> bool {
        self.all_transactions.contains(tx_hash)
    }

    pub(crate) fn insert_tx(
        &mut self,
        transaction: TxEnvelope,
        on_chain_balance: U256,
        on_chain_nonce: u64,
    ) -> InsertResult {

        let transaction = Arc::new(transaction);

        // Get the Signed<TxEip1559> type
        let signed_tx = match &*transaction {
            TxEnvelope::Eip1559(signed_tx) => Ok(signed_tx),
            _ => Err(InsertErr::UnknownTransactionType)
        }?;

        // Get the TxEip1559 type so we can access its properties (ie gas_limit, nonce etc)
        let unsigned_tx = signed_tx.tx();

        // Get transaction signer
        let signer = &transaction
            .recover_signer()
            .map_err(|_| InsertErr::SignatureError)?;
        // Get nonce
        let tx_nonce = unsigned_tx.nonce;
        // Get gas_limit
        let gas_limit = unsigned_tx.gas_limit();


        // Validate the transaction
        // Checks the following:
        // - enough transaction slots for user
        // - tx_gas_limit > block_gas_limit
        // - on_chain_nonce <= tx_nonce
        let transaction = self.ensure_valid(Arc::clone(&transaction), gas_limit, &signer, on_chain_nonce, tx_nonce)?;


        // Create TransactionId
        let transaction_id = TransactionId {
            sender: signer.clone(),
            nonce: tx_nonce

        };

        let mut state = TxState::default();
        // TODO: Check this
        let mut cumulative_cost = U256::ZERO;
        let mut updates = Vec::new();

        // Tx does not exceed block gas limit, checked in ensure_valid
        state.insert(TxState::NOT_TOO_MUCH_GAS);

        // TransactionId of the ancestor transaction. Will be None if the transaction nonce matches the on_chain_nonce
        let ancestor = TransactionId::ancestor(
            tx_nonce,
            on_chain_nonce,
            *signer
        );

        if !transaction.is_eip4844() {
            // Non Eip844 transactions always satisfy blob fee cap condition
            // Non-EIP4844 transaction always satisfy the blob fee cap condition
            state.insert(TxState::ENOUGH_BLOB_FEE_CAP_BLOCK);
        } else {
            // handle Eip844 transaction
            // ...
        }

        // If there's no ancestor tx then this is the next transaction to be executed
        if ancestor.is_none() {
            state.insert(TxState::NO_NONCE_GAPS);
            state.insert(TxState::NO_PARKED_ANCESTORS);
        }

        // TODO: Check this
        // Check dynamic fee
        let fee_cap = transaction.max_fee_per_gas();

        if fee_cap < self.config.minimal_protocol_basefee as u128 {
            return Err(InsertErr::FeeCapBelowMinimumProtocolFeeCap { fee_cap })
        }
        if fee_cap >= self.config.pending_base_fee as u128 {
            state.insert(TxState::ENOUGH_FEE_CAP_BLOCK);
        }

        // placeholder for the replaced transaction, if any
        let mut replaced_tx = None;

        let pool_tx = PoolInternalTransaction {
            transaction: Arc::clone(&transaction),
            subpool: state.into(),
            state,
            cumulative_cost,
        };

        // Attempt to insert the transaction
        match self.all_transactions.txs.entry(transaction_id) {
            Entry::Vacant(entry) => {
                // Insert the transaction in both maps
                self.all_transactions.by_hash.insert(*pool_tx.transaction.tx_hash(), pool_tx.transaction.clone());
                entry.insert(pool_tx.into());
            }
            Entry::Occupied(mut entry) => {
                // Transaction with the same nonce already exists: replacement candidate
                let existing_transaction = entry.get().transaction.as_ref();

                // Get the Signed<TxEip1559> type for existing transaction
                let signed_existing_tx_ref = match existing_transaction {
                    TxEnvelope::Eip1559(signed_tx) => Ok(signed_tx),
                    _ => Err(InsertErr::UnknownTransactionType)
                }?;
            
                // Get the TxEip1559 type for existing transaction
                let unsigned_existing_tx_ref = signed_existing_tx_ref.tx();

                let existing_max_fee_per_gas = unsigned_existing_tx_ref.max_fee_per_gas;

                // Ensure the new transaction is not underpriced
                if Self::is_underpriced(existing_max_fee_per_gas, unsigned_tx.max_fee_per_gas)
                {
                    return Err(InsertErr::Underpriced {
                        existing: *existing_transaction.tx_hash(),
                    })
                }
                let new_hash = *pool_tx.transaction.tx_hash();
                let new_transaction = pool_tx.transaction.clone();
                let replaced = entry.insert(pool_tx.into());
                self.all_transactions.by_hash.remove(replaced.transaction.tx_hash());
                self.all_transactions.by_hash.insert(new_hash, new_transaction);
                // also remove the hash
                replaced_tx = Some((replaced.transaction, replaced.subpool));
            }
        }

        // TransactionId of the next transaction according to the on-chain nonce
        let on_chain_id = TransactionId::new(*signer, on_chain_nonce);

        {
            // get all transactions of the sender's account
            let mut descendants = self.all_transactions.descendant_txs_mut(&on_chain_id).peekable();

            // Tracks the next nonce we expect if the transactions are gapless
            let mut next_nonce = on_chain_id.nonce;

            // TODO: Double check this bug
            // We need to find out if the next transaction of the sender is considered pending
            // NOTE: Phill: This is a bug. We cannot find ancestors using descendants! (L1658)
            // All comments below are mine
            // Result: If the current tx's nonce matched the on-chain nonce, will be false (L1642)
            // If the current tx had ancestors, will always be true (see bug on L1658)
            let mut has_parked_ancestor = if ancestor.is_none() {
                // If it doesn't have any ancestors (tx that need to execute before)
                // the new transaction is the next one
                false
            } else {
                // Otherwise, it has ancestors (ie txs that need to execute).
                // The transaction was added above so the _inclusive_ descendants iterator
                // returns at least 1 tx (as it includes the tx that was just added! (ie this current one))
                // descendants.peek() allows us to look at the tx with the next highest nonce after this current one
                let (id, tx) = descendants.peek().expect("includes >= 1");
                // If the id of the next descendant
                // is less than the current tx (inserted_tx)
                // then we flip (but don't set) and return the is_pending flag of the descendant tx.
                // This makes no sense as descendants have a larger nonce and 
                // for the current tx to have a smaller nonce it would be an ancestor.
                if id.nonce < tx_nonce {
                    // tx here is the next descendant of the current tx.
                    !tx.state.is_pending()
                } else {
                    true
                }
            };



        // Traverse all transactions of the sender and update existing transactions
            // NOTE: Phill: This is where we ensure that txs are added without gaps
            // We are iterating through the descendants. When we go through the loop,
            // we first check if the current nonce is equal to the expected nonce.
            // If it is, we continue, otherwise break.
            // At the end of the loop, we update to the next expected nonce,
            // therefore ensuring that there are no nonce gaps.
            for (id, tx) in descendants {
                let current_pool = tx.subpool;

                // If there's a nonce gap, we can shortcircuit
                // This nonce check is basically checking if there is
                //  a continuous thread of nonces in the txs BTMap (which holds all txs) 
                // that starts with the current ocNonce.
                // So we continue if the current descendant is part of that chain.
                if next_nonce != id.nonce {
                    break
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
            transaction: Arc::clone(&transaction), 
            move_to: state.into(), 
            state, 
            replaced_tx, 
            updates 
        })
    }

    /// Validation checks for new transaction
    /// 
    /// Enforces additional rules:
    /// - Spam protection: reject transactions from senders that have exhausted their slot capacity
    /// - Gas limit: reject transactions that exceed a block's maximum gas
    fn ensure_valid(
    &self,
    transaction: Arc<TxEnvelope>,  // Take an Arc by value
    tx_gas_limit: u64,
    signer: &Address,
    on_chain_nonce: u64,
    tx_nonce: u64
    ) -> Result<Arc<TxEnvelope>, InsertErr> {  // Return an Arc instead of a reference
        let user_tx_count = self.all_transactions.tx_counter.get(signer).copied().unwrap_or_default();

        if user_tx_count >= self.config.max_account_slots {
            return Err(InsertErr::ExceededSenderTransactionsCapacity {
                address: signer.clone(),
            })
        }

        if tx_gas_limit > self.config.block_gas_limit {
            return Err(InsertErr::TxGasLimitMoreThanAvailableBlockGas {
                block_gas_limit: self.config.block_gas_limit,
                tx_gas_limit,
            })
        }

        if on_chain_nonce <= tx_nonce {
            return Err(InsertErr::InvalidTxNonce {
                on_chain_nonce,
                tx_nonce,
            })
        }

        Ok(transaction)
    }


    fn is_underpriced(existing_max_fee_per_gas: u128, possible_replacement_max_fee_per_gas: u128) -> bool {
        possible_replacement_max_fee_per_gas <  existing_max_fee_per_gas
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
        let tx = match pool {
            SubPool::Queued => self.queued_transactions.remove_transaction(tx),
            SubPool::Pending => self.pending_transactions.remove_transaction(tx),
        };

        tx
    }

    /// Inserts the transaction into the given sub-pool.
    fn add_transaction_to_subpool(
        &mut self,
        pool: SubPool,
        tx: Arc<TxEnvelope>,
    ) {
        match pool {
            SubPool::Queued => self.queued_transactions.add_transaction(tx),
            SubPool::Pending => {
                self.pending_transactions.add_transaction(tx, self.config.pending_base_fee);
            }
        }
    }

    /// Maintenance task to apply a series of updates.
    ///
    /// This will move/discard the given transaction according to the `PoolUpdate`
    fn process_updates(&mut self, updates: Vec<PoolUpdate>) -> UpdateOutcome {
        let mut outcome = UpdateOutcome::default();
        for PoolUpdate { id, hash, current, destination } in updates {
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
    /// [`Self::on_canonical_state_change`]
    fn prune_transaction_by_hash(
        &mut self,
        tx_hash: &B256,
    ) -> Option<Arc<TxEnvelope>> {
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
}

/// The internal transaction typed used by `Pool` which contains additional info used for
/// determining the current state of the transaction.
#[derive(Debug)]
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
    /// Used to sum the cost of all transactions to update PoolInternalTransaction.cumulative_cost
    fn next_cumulative_cost(&self) -> U256 {
        self.cumulative_cost + &self.cost()
    }

    /// Returns the cost that this transaction is allowed to consume:
    ///
    /// For EIP-1559 transactions: `max_fee_per_gas * gas_limit + tx_value`.
    fn cost(&self) -> U256 {
        // System currently only handles Eip1559 txs
        let signed_tx = self.transaction.as_eip1559().expect("Unknown transaction type");
        let unsigned_tx = signed_tx.tx();

        let max_fee_per_gas = unsigned_tx.max_fee_per_gas;
        let gas_limit = unsigned_tx.gas_limit;
        let value = unsigned_tx.value;

        U256::from(max_fee_per_gas) * U256::from(gas_limit) + value
    }
}