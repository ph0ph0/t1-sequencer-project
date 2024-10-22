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
use alloy::primitives::aliases::TxHash;


// TODO: Add derive
pub struct PoolConfig {
    /// Max number of transactions a user can have in the pool
    pub max_account_slots: usize,
    pub block_gas_limit: u64
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

        // TODO: Add match statement
        self.insert_tx(tx, on_chain_balance, on_chain_nonce);

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
        
        // Get the Signed<TxEip1559> type
        let signed_tx_ref = match transaction {
            TxEnvelope::Eip1559(signed_tx) => Ok(signed_tx),
            _ => Err(InsertErr::UnknownTransactionType { transaction: Arc::new(transaction) })
        }?;

        // Get the TxEip1559 type
        let unsigned_tx_ref = signed_tx_ref.tx();

        assert!(on_chain_nonce <= unsigned_tx_ref.nonce, "Invalid transaction");

        // Convert transaction to underlying Transaction type
        let signer = transaction
            .recover_signer()
            .map_err(|signature_error| InsertErr::SignatureError { signature_error })?;

        let transaction = self.ensure_valid(&unsigned_tx_ref.gas_limit(), &signer)?;


        // TODO: Return correct result
        Ok(InsertOk{transaction, move_to: state.into(), state, replaced_tx, updates})
    }

    /// Validation checks for new transaction
    /// 
    /// Enforces additional rules:
    /// - Spam protection: reject transactions from senders that have exhausted their slot capacity
    /// - Gas limit: reject transactions that exceed a block's maximum gas
    fn ensure_valid(
        &self,
        tx_gas_limit: u64,
        signer: &Address,
        transaction: TxEnvelope
    ) -> Result<TxEnvelope, InsertErr> {
        let user_tx_count = self.all_transactions.tx_counter.get(signer).copied().unwrap_or_default();

        if user_tx_count >= self.config.max_account_slots {
            return Err(InsertErr::ExceededSenderTransactionsCapacity { transaction: Arc::new(transaction) })
        }

        if tx_gas_limit > self.config.block_gas_limit {
            return Err(InsertErr::TxGasLimitMoreThanAvailableBlockGas {
                block_gas_limit: self.config.block_gas_limit,
                tx_gas_limit,
                transaction: Arc::new(transaction),
            })
        }
        Ok(transaction)
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

/// Identifier for the transaction Sub-pool
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[repr(u8)]
pub enum SubPool {
    // Queued pool holds transactions that cannot be added to Pending due to nonce gaps or lack of funds
    Queued = 0,
    // Pending pool contains transactions that can be executed on the current statex
    Pending
}

pub(crate) type InsertResult = Result<InsertOk, InsertErr>;

pub struct InsertOk {
    /// Reference to the transaction
    tranasction: Arc<TxEnvelope>,
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
    /// Unkown transaction error, currently only Eip1559 transactions are handled
    UnknownTransactionType { transaction: Arc<TxEnvelope> },
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
    txs: BTreeMap<TransactionId, TxEnvelope>,
    /// All transactions in the pool ordered by hash
    by_hash: HashMap<TxHash, TxEnvelope>,
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

    pub fn ancestor(&self, on_chain_nonce: u64) -> Option<Self>{
        (self.nonce > on_chain_nonce)
            .then(|| Self::new(self.sender, self.nonce.saturating_sub(1)))
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