// -----sequence.rs-----

use std::collections::{BTreeSet, BTreeMap, HashMap};
use std::cmp::{Ordering};
use alloy::primitives::Address;
use std::sync::Arc;
use alloy::consensus::TxEnvelope;

pub struct TransactionSequence<O>
where
    O: TransactionOrdering + PartialEq + Eq + PartialOrd + Ord,
{
    ordering: O,
    sequenced_transactions: BTreeSet<PendingTransaction<O>>,
    // nonce_map: HashMap<u64, u64>, //TODO: Remove
    sum_priority_fee: u128,
}

// ------pool.rs-----

use std::collections::hash_map;
use std::collections::btree_map::Entry;
use alloy::primitives::aliases::TxHash;


// TODO: Add derive
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
    queued_transactions: QueuedPool<QueuedOrdering>,
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
        // Check to see if the new tx already exists in the pool
        if self.contains(tx.tx_hash()) {
            return Err(PoolError::new(*tx.tx_hash(), PoolErrorKind::AlreadyImported))
        }

        // TODO: Update user info?


        match self.insert_tx(tx, on_chain_balance, on_chain_nonce) {
            Ok(InsertOk {transaction, move_to, replaced_tx, updates, ..}) => {

            }
            Err(err) => {

            }
        }

        // TODO: Return correct result
        Ok(AddedTransaction::Pending(tx))
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
            _ => Err(InsertErr::UnknownTransactionType { transaction: Arc::clone(&transaction) })
        }?;

        // Get the TxEip1559 type so we can access its properties (ie gas_limit, nonce etc)
        let unsigned_tx = signed_tx.tx();

        // Get transaction signer
        let signer = &transaction
            .recover_signer()
            .map_err(|signature_error| InsertErr::SignatureError { signature_error })?;
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
            return Err(InsertErr::FeeCapBelowMinimumProtocolFeeCap { transaction, fee_cap })
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
                    _ => Err(InsertErr::UnknownTransactionType { transaction: Arc::clone(&transaction) })
                }?;
            
                // Get the TxEip1559 type for existing transaction
                let unsigned_existing_tx_ref = signed_existing_tx_ref.tx();

                let existing_max_fee_per_gas = unsigned_existing_tx_ref.max_fee_per_gas;

                // Ensure the new transaction is not underpriced
                if Self::is_underpriced(existing_max_fee_per_gas, unsigned_tx.max_fee_per_gas)
                {
                    return Err(InsertErr::Underpriced {
                        transaction: Arc::clone(&pool_tx.transaction),
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
            return Err(InsertErr::ExceededSenderTransactionsCapacity { transaction: transaction })
        }

        if tx_gas_limit > self.config.block_gas_limit {
            return Err(InsertErr::TxGasLimitMoreThanAvailableBlockGas {
                block_gas_limit: self.config.block_gas_limit,
                tx_gas_limit,
                transaction: transaction,
            })
        }

        if on_chain_nonce <= tx_nonce {
            return Err(InsertErr::InvalidTxNonce {
                on_chain_nonce,
                tx_nonce,
                transaction
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
            self.remove_from_subpool(replaced_pool, replaced.id());
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
            SubPool::Queued => self.queued_pool.remove_transaction(tx),
            SubPool::Pending => self.pending_pool.remove_transaction(tx),
        };

        if let Some(ref tx) = tx {
            // We trace here instead of in subpool structs directly, because the `ParkedPool` type
            // is generic and it would not be possible to distinguish whether a transaction is
            // being removed from the `BaseFee` pool, or the `Queued` pool.
            trace!(target: "txpool", hash=%tx.transaction.hash(), ?pool, "Removed transaction from a subpool");
        }
        tx
    }

    /// Inserts the transaction into the given sub-pool.
    fn add_transaction_to_subpool(
        &mut self,
        pool: SubPool,
        tx: Arc<ValidPoolTransaction<T::Transaction>>,
    ) {
        // We trace here instead of in structs directly, because the `ParkedPool` type is
        // generic and it would not be possible to distinguish whether a transaction is being
        // added to the `BaseFee` pool, or the `Queued` pool.
        trace!(target: "txpool", hash=%tx.transaction.hash(), ?pool, "Adding transaction to a subpool");
        match pool {
            SubPool::Queued => self.queued_pool.add_transaction(tx),
            SubPool::Pending => {
                self.pending_pool.add_transaction(tx, self.all_transactions.pending_fees.base_fee);
            }
            SubPool::BaseFee => self.basefee_pool.add_transaction(tx),
            SubPool::Blob => self.blob_pool.add_transaction(tx),
        }
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

// TODO: Move this somewhere that makes sense
pub enum AddedTransaction
{
    Pending(TxEnvelope),

    Queued {
        transaction: TxEnvelope,
        replaced: Option<TxEnvelope>,
        subpool: SubPool
    }
}

pub(crate) type InsertResult = Result<InsertOk, InsertErr>;

pub struct InsertOk {
    /// Reference to the transaction
    transaction: Arc<TxEnvelope>,
    /// The pool to move the transaction to
    move_to: SubPool,
    /// State of the inserted transaction
    state: TxState,
    /// The transaction that was replaced
    replaced_tx: Option<(Arc<TxEnvelope>, SubPool)>,
    /// Additional updates to transactions affected by this change
    updates: Vec<PoolUpdate>
}

pub(crate) enum InsertErr {
    /// Unknown transaction error, currently only Eip1559 transactions are handled
    UnknownTransactionType { transaction: Arc<TxEnvelope> },
    /// On-chain nonce must be less than or equal to the transaction nonce
    InvalidTxNonce {
        on_chain_nonce: u64,
        tx_nonce: u64,
        transaction: Arc<TxEnvelope>
    },
    /// Error in the signature of the transaction
    SignatureError {signature_error: SignatureError},
    /// Attempted to replace existing transaction, but was underpriced
    Underpriced {
        transaction: Arc<TxEnvelope>,
        #[allow(dead_code)]
        existing: TxHash,
    },
    /// Attempted to insert a transaction that would overdraft the sender's balance at the time of
    /// insertion.
    Overdraft { transaction: Arc<TxEnvelope> },
    /// The transactions feeCap is lower than the chain's minimum fee requirement.
    ///
    /// See also [`MIN_PROTOCOL_BASE_FEE`]
    FeeCapBelowMinimumProtocolFeeCap { transaction: Arc<TxEnvelope>, fee_cap: u128 },
    /// Sender currently exceeds the configured limit for max account slots.
    ///
    /// The sender can be considered a spammer at this point.
    ExceededSenderTransactionsCapacity { transaction: Arc<TxEnvelope> },
    /// Transaction gas limit exceeds block's gas limit
    TxGasLimitMoreThanAvailableBlockGas {
        transaction: Arc<TxEnvelope>,
        block_gas_limit: u64,
        tx_gas_limit: u64,
    },
}


// -----all_transactions.rs----

use alloy::primitives::SignatureError;

pub struct AllTransactions
where 
{
    /// All transactions in the pool, grouped by sender, orderd by nonce
    txs: BTreeMap<TransactionId, PoolInternalTransaction>,
    /// All transactions in the pool ordered by hash
    by_hash: HashMap<TxHash, Arc<TxEnvelope>>,
    /// Keeps track of the number of transactions by sender currently in the system
    tx_counter: HashMap<Address, usize>,
}

impl AllTransactions
{
    /// Creates new instance
    fn new(&self) -> Self {
        Self {
            txs: BTreeMap::new(),
            by_hash: HashMap::new(),
            tx_counter: HashMap::new()
        }
    }

    pub(crate) fn contains(&self, tx_hash: &TxHash) -> bool {
        self.by_hash.contains_key(tx_hash)
    }

    pub(crate) fn tx_inc(&mut self, sender: Address) {
        let count = self.tx_counter.entry(sender).or_default();
        *count += 1;
    }

    pub(crate) fn tx_decr(&mut self, sender: Address) {
        if let hash_map::Entry::Occupied(mut entry) = self.tx_counter.entry(sender) {
            let count = entry.get_mut();

            if *count == 1 {
                entry.remove();
                return;
            }
            *count -= 1;
        }
    }

    /// Returns all mutable transactions that _follow_ after the given id but have the same sender.
    ///
    /// NOTE: The range is _inclusive_: if the transaction that belongs to `id` it field be the
    /// first value.
    pub(crate) fn descendant_txs_mut<'a, 'b: 'a>(
        &'a mut self,
        id: &'b TransactionId,
    ) -> impl Iterator<Item = (&'a TransactionId, &'a mut PoolInternalTransaction)> + 'a {
        self.txs.range_mut(id..).take_while(|(other, _)| id.sender == other.sender)
    }

    // TODO:
    // pub(crate) update(
    //     &mut self,
    //     changed_accounts: HashMap<Address, SenderInfo>
    // ) -> Vec<PoolUpdate> {

    // }
}



// -----updates.rs

// A change of the transaction's location
///
/// NOTE: this guarantees that `current` and `destination` differ.
#[derive(Debug)]
pub(crate) struct PoolUpdate {
    /// Internal tx id.
    pub(crate) id: TransactionId,
    /// Hash of the transaction.
    pub(crate) hash: TxHash,
    /// Where the transaction is currently held.
    pub(crate) current: SubPool,
    /// Where to move the transaction to.
    pub(crate) destination: Destination,
}

/// Where to move an existing transaction.
#[derive(Debug)]
pub(crate) enum Destination {
    /// Discard the transaction.
    Discard,
    /// Move transaction to pool
    Pool(SubPool),
}

// -----pending.rs-----

#[derive(Eq, PartialEq)]
pub struct PendingTransaction<O>
where
    O: TransactionOrdering + PartialEq + Eq + PartialOrd + Ord,
{
    submission_id: u64,
    transaction: TxEnvelope,
    priority: Priority<O::PriorityValue>,
    // alloy Transaction type doesn't contain a sender field, so we must extract it from the TxEnvelope
    sender: Address
}

impl<O> Ord for PendingTransaction<O> 
where
    O: TransactionOrdering + PartialEq + Eq + PartialOrd + Ord,
{
    // TODO: Probs need to remove the nonce sort as it is not needed
    fn cmp(&self, other: &Self) -> Ordering {
        // Primary sort by priority fee (descending)
        other.priority.cmp(&self.priority)
            // Secondary sort by address
            .then(self.sender.cmp(&other.sender))
    }
}

impl<O> PartialOrd for PendingTransaction<O> 
where
    O: TransactionOrdering + PartialEq + Eq + PartialOrd + Ord,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}



// TODO: Add derive
pub struct PendingPool<O> 
where
    O: TransactionOrdering + PartialEq + Eq + PartialOrd + Ord,
{
    /// Determines how the transactions will be ordered
    ordering: O,
    /// Assigned to each tx, used to determine when transactions were added to the pool
    submission_id: u64,
    /// All the transactions in the pool grouped by their sender and ordered by nonce
    by_id: BTreeMap<TransactionId, PendingTransaction<O>>,
    /// All transactions sorted by priority
    all: BTreeSet<PendingTransaction<O>>
}

// -----queued.rs-----

#[derive(PartialOrd, Eq, PartialEq)]
pub struct QueuedPoolTransaction<T: QueuedOrd> {

    /// Id to indicate when transaction was added to pool
    submission_id: u64,
    /// The transaction
    transaction: T
}

impl<T: QueuedOrd> Ord for QueuedPoolTransaction<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        // First, compare transactions by their own Ord impl (see `impl Ord for QueuedOrdering`)
        // Then compare the submission_ids.
        self.transaction
            .cmp(&other.transaction)
            .then_with(|| other.submission_id.cmp(&self.submission_id))
    }
}

pub trait QueuedOrd: Ord {
    type Transaction: alloy::consensus::Transaction;
}

/// Type wrapper for an alloy TxEnvelope in the queue, allowing them to be ordered by max_fee_per_gas then submission_id (see Ord implemntation below and impl<T: QueuedOrd> Ord for QueuedPoolTransaction<T>)
pub struct QueuedOrdering(TxEnvelope);

impl QueuedOrdering {
    pub fn max_fee_per_gas(&self) -> u128 {
        self.0.max_fee_per_gas()
    }
}

impl Ord for QueuedOrdering {
    // Sort in reverse order (ie higher gas fees towards end of set)
    fn cmp(&self, other: &Self) -> Ordering {
        other.max_fee_per_gas()
            .cmp(&self.max_fee_per_gas())
    }
}

impl PartialOrd for QueuedOrdering {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for QueuedOrdering {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for QueuedOrdering {}

impl QueuedOrd for QueuedOrdering {
    // TODO: Is this needed
    type Transaction = TxEnvelope;
}


// TODO: Derive
pub struct QueuedPool<T: QueuedOrd> {
    /// Keeps track of the last transaction submitted to the pool
    current_submission_id: u64,
    /// All transaction currently inside the pool grouped by sender and ordered by nonce
    by_id: BTreeMap<TransactionId, QueuedPoolTransaction<T>>,
    /// All transactions sorted by their order function. The higher the better.
    best: BTreeSet<QueuedPoolTransaction<T>>,

    /// Last submission_id for each sender, TODO: Do we need this?
    // last_sender_submission: BTreeSet<SubmissionSenderId>>,

    // TODO: Move up to Pool?
    // Keeps track of the number of transactions in the pool by the sender and the last submission id.
    sender_transaction_count: HashMap<Address, SenderTransactionCount>
}

impl<T: QueuedOrd> QueuedPool<T> {
    fn remove_transaction(&mut self, id: &TransactionId) -> Option<Arc<TxEnvelope>> {
        let tx = self.by_id.remove(id)?;
        self.best.remove(&tx);
        self.remove_sender_count(tx.transaction.recover_signer());
        Some(tx.into())
    }
}


// -----identifiers.rs-----

/// A unique identifier of a transaction of a Sender.
///
/// This serves as an identifier for dependencies of a transaction:
/// A transaction with a nonce higher than the current state nonce depends on `tx.nonce - 1`.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct TransactionId {
    /// Sender of this transaction
    sender: Address,
    /// Nonce of this transaction
    nonce: u64
}

impl TransactionId {
    pub const fn new(sender: Address, nonce: u64) -> Self {
        Self {
            sender,
            nonce
        }
    }

    pub fn ancestor(tx_nonce: u64, on_chain_nonce: u64, signer: Address) -> Option<Self>{
        (tx_nonce > on_chain_nonce)
            .then(|| Self::new(signer, tx_nonce.saturating_sub(1)))
    }

    pub fn unchecked_ancestor(&self) -> Option<Self> {
        (self.nonce != 0)
            .then(|| Self::new(self.sender, self.nonce - 1))
    }

    pub const fn descendant(&self) -> Self {
        Self::new(self.sender, self.next_nonce())
    }

    #[inline]
    pub const fn next_nonce(&self) -> u64 {
        self.nonce + 1
    }
}

// TODO: used?
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SenderTransactionCount {
    count: u64,
    last_submission: u64
}

// -----ordering.rs-----

use std::{fmt, marker::PhantomData};
use alloy::{
    consensus::Transaction,
    primitives::U256
};

pub trait TransactionOrdering: Send + Sync + 'static {
    
    type PriorityValue: Ord + Clone + Default + fmt::Debug + Send + Sync;

    fn priority(
        &self,
        transaction: &TxEnvelope,
        base_fee: u64,
    ) -> Priority<Self::PriorityValue>;
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub enum Priority<T: Ord + Clone> {
    Value(T),
    None,
}

impl<T: Ord + Clone> From<Option<T>> for Priority<T> {
    fn from(value: Option<T>) -> Priority<T> {
        value.map_or(Self::None, Priority::Value)
    }
}

pub struct CoinbaseTipOrdering<T>(PhantomData<T>);

impl<T> TransactionOrdering for CoinbaseTipOrdering<T> 
where   
    T: Transaction + 'static,
{
    
    type PriorityValue = U256;

    fn priority(
        &self,
        transaction: &TxEnvelope,
        base_fee: u64,
    ) -> Priority<Self::PriorityValue> {
        // If the **effective** tip is zero, return Priority::None
        transaction.effective_tip_per_gas(base_fee)
            .map(U256::from)
            .and_then(|tip| if tip.is_zero() {None} else {Some(tip)})
            .map_or(Priority::None, Priority::Value)
    }
}

impl<T> Default for CoinbaseTipOrdering<T> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<T> Clone for CoinbaseTipOrdering<T> {
    fn clone(&self) -> Self {
        Self::default()
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn test_coinbase_tip_ordering_priority_with_default_fees() {
//         // Scenario: max_fee_priority_fee_per_gas == MockTransaction default value
//         // Expect: Priority::Value(expected)
//         let tx = MockTransaction::eip1559();
//         let ordering: CoinbaseTipOrdering<MockTransaction> = CoinbaseTipOrdering::default();
//         let base_fee = 3;

//         let priority = ordering.priority(&tx, base_fee);
//         let expected = U256::from(tx.get_max_fee().unwrap() as u64 - base_fee);

//         assert_eq!(priority, Priority::Value(expected), "Expected Priority::Value");
//     }

//     #[test]
//     fn test_coinbase_tip_ordering_zero_priority_fee() {
//         // Scenario: max_fee_priority_fee_per_gas == 0
//         // Expect: Priority::None since the **effective** tip is calculated (ie tip = min(max_fee - base_fee, max_priority_fee)) 
//         let tx = MockTransaction::eip1559().with_priority_fee(0);
//         let ordering: CoinbaseTipOrdering<MockTransaction> = CoinbaseTipOrdering::default();
//         let base_fee = 3;

//         let priority = ordering.priority(&tx, base_fee);

//         assert_eq!(Priority::None, priority, "Expected Priority::None, got Priority::Value");
//     }

//     #[test]
//     fn test_coinbase_tip_ordering_max_priority_fee() {
//         // Scenario: max_fee_priority_fee_per_gas == u128::MAX
//         // Expect: Priority::Value(max_fee - base_fee) 
//         let tx = MockTransaction::eip1559().with_priority_fee(u128::MAX);
//         let ordering: CoinbaseTipOrdering<MockTransaction> = CoinbaseTipOrdering::default();
//         let base_fee = 1;

//         let priority = ordering.priority(&tx, base_fee);
//         let expected = U256::from(tx.get_max_fee().unwrap() as u64 - base_fee);

//         assert_eq!(priority, Priority::Value(expected), "Expected Priority::Value");
//     }

//     #[test]
//     fn test_coinbase_tip_ordering_base_fee_higher_than_max_fee() {
//         // Scenario: base_fee > max_fee_per_gas
//         // Expect: Priority::None since the **effective** tip is calculated (ie tip = min(max_fee - base_fee, max_priority_fee)) 
//         let tx = MockTransaction::eip1559().with_max_fee(0);
//         let ordering: CoinbaseTipOrdering<MockTransaction> = CoinbaseTipOrdering::default();
//         let base_fee = 3;

//         let priority = ordering.priority(&tx, base_fee);
//         assert!(matches!(priority, Priority::None), "Expected Priority::None");
//     }

//     #[test]
//     fn test_coinbase_tip_ordering_max_fee() {
//         // Scenario: max_fee_priority_fee_per_gas == u128::MAX
//         // Expect: Priority::Value(max_fee - base_fee) 
//         let tx = MockTransaction::eip1559().with_max_fee(u128::MAX);
//         let ordering: CoinbaseTipOrdering<MockTransaction> = CoinbaseTipOrdering::default();
//         let base_fee = 1;

//         let priority = ordering.priority(&tx, base_fee);
//         let expected = U256::from(tx.get_priority_fee().unwrap());

//         assert_eq!(priority, Priority::Value(expected), "Expected Priority::Value");
//     }
// }

// error.rs

use thiserror;

/// Transaction pool result type.
pub type PoolResult<T> = Result<T, PoolError>;

/// Transaction pool error
#[derive(Debug, thiserror::Error)]
#[error("[{hash}]: {kind}")]
pub struct PoolError {
    /// Hash of the transaction that caused the error
    pub hash: TxHash,
    /// The kind of error
    pub kind: PoolErrorKind
}

impl PoolError {
    fn new(hash: TxHash, kind: PoolErrorKind) -> Self {
        Self {
            hash,
            kind
        }
    }
}

/// The kind of pool error 
#[derive(Debug, thiserror::Error)]
pub enum PoolErrorKind {
    // Transaction already exists in the pool
    #[error("already imported")]
    AlreadyImported,

    // Currently the implementation only handles Eip1559 txs
    #[error("unknown transaction type")]
    UnknownTransactionType,
}


// -----test_utils/mock.rs-----

use alloy::consensus::{
    //Transaction,
    // TxEnvelope,
    TxType
};
use alloy::primitives::{
    B256, 
    // Address, 
    ChainId, 
    // U256, 
    TxKind, 
    Bytes,
    FixedBytes
};
use alloy::eips::{
    eip2930::AccessList,
    eip7702::SignedAuthorization,
};

/// A Bare transaction type used for testing.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum MockTransaction {
    /// Eip1559 transaction type
    Eip1559 {
        /// The chain id of the transaction
        chain_id: ChainId,
        /// The hash of the transaction
        hash: B256, 
        /// The sender's address
        sender: Address,
        /// The transaction nonce
        nonce: u64,
        /// The maximum fee per gas for the transaction
        max_fee_per_gas: u128,
        /// The maximum priority fee per gas for the transaction
        max_priority_fee_per_gas: u128,
        /// The gas limit for the transaction
        gas_limit: u64,
        /// The transaction's destination address
        to: TxKind,
        /// The value of the transaction
        value: U256,
        /// The access list for the transaction
        access_list: AccessList,
        /// The transaction input data
        input: Bytes,        
    }
}

impl MockTransaction {
    pub fn eip1559() -> Self {
        Self::Eip1559{
            chain_id: 1,
            hash: B256::random(),
            sender: Address::random(),
            nonce: 0,
            max_fee_per_gas: 7,
            max_priority_fee_per_gas: 4,
            gas_limit: 0,
            to: Address::random().into(),
            value: Default::default(),
            input: Bytes::new(),
            access_list: Default::default(),
        }
    }

    pub fn set_priority_fee(&mut self, val: u128) -> &mut Self {
        match self {
            Self::Eip1559 { max_priority_fee_per_gas, .. } => {
                *max_priority_fee_per_gas = val;
            }
        }
        self
    }

    pub fn with_priority_fee(mut self, val: u128) -> Self{
        self.set_priority_fee(val);
        self
    }

    pub const fn get_priority_fee(&self) -> Option<u128> {
        match self {
            Self::Eip1559 { max_priority_fee_per_gas, .. } => Some(*max_priority_fee_per_gas),
        }
    }

    pub fn set_max_fee(&mut self, val: u128) -> &mut Self {
        match self {
            Self::Eip1559 { max_fee_per_gas, .. } => {
                *max_fee_per_gas = val;
            }
        }
        self
    }
    
    pub fn with_max_fee(mut self, val: u128) -> Self {
        self.set_max_fee(val);
        self
    }

    pub const fn get_max_fee(&self) -> Option<u128> {
        match self {
            Self::Eip1559 { max_fee_per_gas, .. } => Some(*max_fee_per_gas),
        }
    }

    /// Simultaneously sets the max fee and max priority fee to the same value for convenience
    pub fn set_gas_price(&mut self, val: u128) -> &mut Self {
        match self {
            Self::Eip1559 { max_fee_per_gas, max_priority_fee_per_gas, .. } => {    
                *max_fee_per_gas = *max_priority_fee_per_gas;
                *max_priority_fee_per_gas = val;
            }
        }
        self
    }

    /// Simultaneously sets the max fee and max priority fee to the same value for convenience
    pub fn with_gas_price(mut self, val: u128) -> Self {
        match self {
            Self::Eip1559 { ref mut max_fee_per_gas, ref mut max_priority_fee_per_gas, .. } => {
                *max_fee_per_gas = val;
                *max_priority_fee_per_gas = val;
            }
        }
        self
    }
    
    pub const fn get_gas_price(&self) -> u128 {
        match self {
            Self::Eip1559 { max_fee_per_gas, .. } => *max_fee_per_gas,
        }
    }

    pub fn set_hash(&mut self, val: B256) -> &mut Self {
        match self {
            Self::Eip1559 { hash, .. } => *hash = val,
        }
        self
    }

    pub fn with_hash(mut self, val: B256) -> Self {
        self.set_hash(val);
        self
    }

    pub const fn get_hash(&self) -> B256 {
        match self {
            Self::Eip1559 { hash, .. } => *hash,
        }
    }

    pub fn set_nonce(&mut self, val: u64) -> &mut Self {
        match self {
            Self::Eip1559 { nonce, .. } => *nonce = val,
        }
        self
    }

    pub fn with_nonce(mut self, val: u64) -> Self {
        self.set_nonce(val);
        self
    }

    pub const fn get_nonce(&self) -> u64 {
        match self {
            Self::Eip1559 { nonce, .. } => *nonce,
        }
    }
    
    /// Returns a clone of the transaction with a new hash and nonce decremented by one
    pub fn prev(&self) -> Self {
        self.clone().with_hash(B256::random()).with_nonce(self.get_nonce() - 1) 
    }

    /// Returns a clone of the transaction with a new hash and nonce incremented by one
    pub fn next(&self) -> Self {
        self.clone().with_hash(B256::random()).with_nonce(self.get_nonce() + 1)
    }

    /// Returns a clone of the transaction with a new hash and nonce incremented by `n`
    pub fn skip(&self, n: u64) -> Self {
        self.clone().with_hash(B256::random()).with_nonce(self.get_nonce() + n)
    }

    /// Returns a clone of the transaction with a new hash and max priority fee incremented by `n`
    pub fn inc_price_by(&self, n: u128) -> Self {
        self.clone().with_hash(B256::random()).with_priority_fee(self.get_priority_fee().unwrap() + n)
    }

    /// Returns a clone of the transaction with a new hash and max priority fee incremented by one
    pub fn inc_price(&self) -> Self {
        self.clone().inc_price_by(1)
    }

    /// Returns a clone of the transaction with a new hash and max priority fee decremented by `n`
    pub fn dec_price_by(&self, n: u128) -> Self {
        self.clone().with_hash(B256::random()).with_priority_fee(self.get_priority_fee().unwrap() - n)
    }

    /// Returns a clone of the transaction with a new hash and max priority fee decremented by one
    pub fn dec_price(&self) -> Self {
        self.clone().dec_price_by(1)
    }

}

// Match statements are used so that the implementation can be extended to other transaction types in the future
impl Transaction for MockTransaction {
    fn chain_id(&self) -> Option<u64> {
        match self {
            MockTransaction::Eip1559 { chain_id, .. } => Some(*chain_id),
        }
    }

    fn nonce(&self) -> u64 {
        match self {
            MockTransaction::Eip1559 {nonce, ..} => *nonce,
        }
    }

    fn gas_limit(&self) -> u64 {
        match self {
            MockTransaction::Eip1559 {gas_limit, ..} => *gas_limit,
        }
    }

    fn gas_price(&self) -> Option<u128> {
        match self {
            MockTransaction::Eip1559 {..} => None,
        }
    }

    fn max_fee_per_gas(&self) ->u128 {
        match self {
            MockTransaction::Eip1559 {max_fee_per_gas, ..} => *max_fee_per_gas,
        }
    }

    fn max_priority_fee_per_gas(&self) -> Option<u128> {
        match self {
            MockTransaction::Eip1559 {max_priority_fee_per_gas, ..} => Some(*max_priority_fee_per_gas),
        }
    }
    
    fn max_fee_per_blob_gas(&self) -> Option<u128> {
        match self {
            MockTransaction::Eip1559 {..} => None,
        }
    }

    fn priority_fee_or_price(&self) -> u128 {
        match self {
            MockTransaction::Eip1559 {max_priority_fee_per_gas, ..} => *max_priority_fee_per_gas,
        }
    }

    fn to(&self) -> TxKind {
        match self {
            MockTransaction::Eip1559 {to, ..} => *to,
        }
    }

    fn value(&self) -> U256 {
        match self {
            MockTransaction::Eip1559 {value, ..} => *value,
        }
    }

    fn input(&self) -> &[u8] {
        match self {
            MockTransaction::Eip1559 {input, ..} => input,
        }
    }
    
    fn ty(&self) -> u8 {
        match self {
            MockTransaction::Eip1559 {..} => TxType::Eip1559 as u8,
        }
    }

    fn access_list(&self) -> Option<&AccessList> {
        match self {
            MockTransaction::Eip1559 {access_list, ..} => Some(access_list),
        }
    }

    fn blob_versioned_hashes(&self) -> Option<&[FixedBytes<32>]> {
        match self {
            MockTransaction::Eip1559 {..} => None,
        }
    }

    fn authorization_list(&self) -> Option<&[SignedAuthorization]> {
        match self {
            MockTransaction::Eip1559 {..} => None,
        }
    }
}

// -----state.rs-----

bitflags::bitflags! {
    /// Marker to represents the current state of a transaction in the pool and from which the corresponding sub-pool is derived, depending on what bits are set.
    ///
    /// This mirrors [erigon's ephemeral state field](https://github.com/ledgerwatch/erigon/wiki/Transaction-Pool-Design#ordering-function).
    ///
    /// The [SubPool] the transaction belongs to is derived from its state and determined by the following sequential checks:
    ///
    /// - If it satisfies the [TxState::PENDING_POOL_BITS] it belongs in the pending sub-pool: [SubPool::Pending].
    /// - If it is an EIP-4844 blob transaction it belongs in the blob sub-pool: [SubPool::Blob].
    /// - If it satisfies the [TxState::BASE_FEE_POOL_BITS] it belongs in the base fee sub-pool: [SubPool::BaseFee].
    ///
    /// Otherwise, it belongs in the queued sub-pool: [SubPool::Queued].
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, PartialOrd, Ord)]
    pub(crate) struct TxState: u8 {
        /// Set to `1` if all ancestor transactions are pending.
        const NO_PARKED_ANCESTORS = 0b10000000;
        /// Set to `1` of the transaction is either the next transaction of the sender (on chain nonce == tx.nonce) or all prior transactions are also present in the pool.
        const NO_NONCE_GAPS = 0b01000000;
        /// Bit derived from the sender's balance.
        ///
        /// Set to `1` if the sender's balance can cover the maximum cost for this transaction (`feeCap * gasLimit + value`).
        /// This includes cumulative costs of prior transactions, which ensures that the sender has enough funds for all max cost of prior transactions.
        const ENOUGH_BALANCE = 0b00100000;
        /// Bit set to true if the transaction has a lower gas limit than the block's gas limit.
        const NOT_TOO_MUCH_GAS = 0b00010000;
        /// Covers the Dynamic fee requirement.
        ///
        /// Set to 1 if `maxFeePerGas` of the transaction meets the requirement of the pending block.
        const ENOUGH_FEE_CAP_BLOCK = 0b00001000;
        /// Covers the dynamic blob fee requirement, only relevant for EIP-4844 blob transactions.
        ///
        /// Set to 1 if `maxBlobFeePerGas` of the transaction meets the requirement of the pending block.
        const ENOUGH_BLOB_FEE_CAP_BLOCK = 0b00000100;
        /// Marks whether the transaction is a blob transaction.
        ///
        /// We track this as part of the state for simplicity, since blob transactions are handled differently and are mutually exclusive with normal transactions.
        const BLOB_TRANSACTION = 0b00000010;

        const PENDING_POOL_BITS = Self::NO_PARKED_ANCESTORS.bits() | Self::NO_NONCE_GAPS.bits() | Self::ENOUGH_BALANCE.bits() | Self::NOT_TOO_MUCH_GAS.bits() |  Self::ENOUGH_FEE_CAP_BLOCK.bits() | Self::ENOUGH_BLOB_FEE_CAP_BLOCK.bits();

        const BASE_FEE_POOL_BITS = Self::NO_PARKED_ANCESTORS.bits() | Self::NO_NONCE_GAPS.bits() | Self::ENOUGH_BALANCE.bits() | Self::NOT_TOO_MUCH_GAS.bits();

        const QUEUED_POOL_BITS  = Self::NO_PARKED_ANCESTORS.bits();

        const BLOB_POOL_BITS  = Self::BLOB_TRANSACTION.bits();
    }
}

// === impl TxState ===

impl TxState {
    /// The state of a transaction is considered `pending`, if the transaction has:
    ///   - _No_ parked ancestors
    ///   - enough balance
    ///   - enough fee cap
    ///   - enough blob fee cap
    #[inline]
    pub(crate) const fn is_pending(&self) -> bool {
        self.bits() >= Self::PENDING_POOL_BITS.bits()
    }

    /// Whether this transaction is a blob transaction.
    #[inline]
    pub(crate) const fn is_blob(&self) -> bool {
        self.contains(Self::BLOB_TRANSACTION)
    }

    /// Returns `true` if the transaction has a nonce gap.
    #[inline]
    pub(crate) const fn has_nonce_gap(&self) -> bool {
        !self.intersects(Self::NO_NONCE_GAPS)
    }
}

/// Identifier for the transaction Sub-pool
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[repr(u8)]
pub enum SubPool {
    // Queued pool holds transactions that cannot be added to Pending due to nonce gaps or lack of funds
    Queued = 0,
    // Pending pool contains transactions that can be executed on the current statex
    Pending
}

// === impl SubPool ===

impl SubPool {
    /// Whether this transaction is to be moved to the pending sub-pool.
    #[inline]
    pub const fn is_pending(&self) -> bool {
        matches!(self, Self::Pending)
    }

    /// Whether this transaction is in the queued pool.
    #[inline]
    pub const fn is_queued(&self) -> bool {
        matches!(self, Self::Queued)
    }

    // /// Whether this transaction is in the base fee pool.
    // #[inline]
    // pub const fn is_base_fee(&self) -> bool {
    //     matches!(self, Self::BaseFee)
    // }

    // /// Whether this transaction is in the blob pool.
    // #[inline]
    // pub const fn is_blob(&self) -> bool {
    //     matches!(self, Self::Blob)
    // }

    /// Returns whether this is a promotion depending on the current sub-pool location.
    #[inline]
    pub fn is_promoted(&self, other: Self) -> bool {
        self > &other
    }
}

impl From<TxState> for SubPool {
    fn from(value: TxState) -> Self {
        if value.is_pending() {
            return Self::Pending
        }
        // if value.is_blob() {
        //     // all _non-pending_ blob transactions are in the blob sub-pool
        //     return Self::Blob
        // }
        if value.bits() < TxState::BASE_FEE_POOL_BITS.bits() {
            return Self::Queued
        }
        // TODO: Double check this
        Self::Queued
        // Self::BaseFee
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn test_promoted() {
//         assert!(SubPool::BaseFee.is_promoted(SubPool::Queued));
//         assert!(SubPool::Pending.is_promoted(SubPool::BaseFee));
//         assert!(SubPool::Pending.is_promoted(SubPool::Queued));
//         assert!(SubPool::Pending.is_promoted(SubPool::Blob));
//         assert!(!SubPool::BaseFee.is_promoted(SubPool::Pending));
//         assert!(!SubPool::Queued.is_promoted(SubPool::BaseFee));
//     }

//     #[test]
//     fn test_tx_state() {
//         let mut state = TxState::default();
//         state |= TxState::NO_NONCE_GAPS;
//         assert!(state.intersects(TxState::NO_NONCE_GAPS))
//     }

//     #[test]
//     fn test_tx_queued() {
//         let state = TxState::default();
//         assert_eq!(SubPool::Queued, state.into());

//         let state = TxState::NO_PARKED_ANCESTORS |
//             TxState::NO_NONCE_GAPS |
//             TxState::NOT_TOO_MUCH_GAS |
//             TxState::ENOUGH_FEE_CAP_BLOCK;
//         assert_eq!(SubPool::Queued, state.into());
//     }

//     #[test]
//     fn test_tx_pending() {
//         let state = TxState::PENDING_POOL_BITS;
//         assert_eq!(SubPool::Pending, state.into());
//         assert!(state.is_pending());

//         let bits = 0b11111100;
//         let state = TxState::from_bits(bits).unwrap();
//         assert_eq!(SubPool::Pending, state.into());
//         assert!(state.is_pending());

//         let bits = 0b11111110;
//         let state = TxState::from_bits(bits).unwrap();
//         assert_eq!(SubPool::Pending, state.into());
//         assert!(state.is_pending());
//     }

//     #[test]
//     fn test_blob() {
//         let mut state = TxState::PENDING_POOL_BITS;
//         state.insert(TxState::BLOB_TRANSACTION);
//         assert!(state.is_pending());

//         state.remove(TxState::ENOUGH_BLOB_FEE_CAP_BLOCK);
//         assert!(state.is_blob());
//         assert!(!state.is_pending());

//         state.insert(TxState::ENOUGH_BLOB_FEE_CAP_BLOCK);
//         state.remove(TxState::ENOUGH_FEE_CAP_BLOCK);
//         assert!(state.is_blob());
//         assert!(!state.is_pending());
//     }
// }
