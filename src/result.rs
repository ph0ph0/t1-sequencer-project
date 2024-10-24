
// -----result.rs-----

use alloy::{
    consensus::TxEnvelope,
    primitives::{Address, TxHash},
};
use std::sync::Arc;
use thiserror;

use crate::{
    identifiers::TransactionId,
    pool::state::{SubPool, TxState},
};

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum AddedTransaction
{
    Pending(AddedPendingTransaction),

    Queued {
        transaction: Arc<TxEnvelope>,
        replaced: Option<Arc<TxEnvelope>>,
        subpool: SubPool
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct AddedPendingTransaction {
    /// Inserted transaction.
    pub transaction: Arc<TxEnvelope>,
    /// Replaced transaction.
    pub replaced: Option<Arc<TxEnvelope>>,
    /// transactions promoted to the pending queue
    pub promoted: Vec<Arc<TxEnvelope>>,
    /// transactions that failed and became discarded
    pub discarded: Vec<Arc<TxEnvelope>>,
}

/// Tracks the result after updating the pool
#[derive(Debug, Eq, PartialEq, Clone)]
pub(crate) struct UpdateOutcome {
    /// transactions promoted to the pending pool
    pub(crate) promoted: Vec<Arc<TxEnvelope>>,
    /// transaction that failed and were discarded
    pub(crate) discarded: Vec<Arc<TxEnvelope>>,
}

impl Default for UpdateOutcome {
    fn default() -> Self {
        Self { promoted: vec![], discarded: vec![] }
    }
}

// A change of the transaction's location
///
/// NOTE: this guarantees that `current` and `destination` differ.
#[derive(Debug, Eq, PartialEq, Clone)]
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
#[derive(Debug, Eq, PartialEq, Clone)]
pub(crate) enum Destination {
    /// Discard the transaction.
    Discard,
    /// Move transaction to pool
    Pool(SubPool),
}

pub(crate) type InsertResult = Result<InsertOk, InsertErr>;

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct InsertOk {
    /// Reference to the transaction
    pub transaction: Arc<TxEnvelope>,
    /// The pool to move the transaction to
    pub move_to: SubPool,
    /// State of the inserted transaction
    pub state: TxState,
    /// The transaction that was replaced
    pub replaced_tx: Option<(Arc<TxEnvelope>, SubPool)>,
    /// Additional updates to transactions affected by this change
    pub updates: Vec<PoolUpdate>
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub(crate) enum InsertErr {
    /// Unknown transaction error, currently only Eip1559 transactions are handled
    UnknownTransactionType,
    /// On-chain nonce must be less than or equal to the transaction nonce
    InvalidTxNonce {
        on_chain_nonce: u64,
        tx_nonce: u64,
    },
    /// Error in the signature of the transaction
    SignatureError,
    /// Attempted to replace existing transaction, but was underpriced
    Underpriced {
        #[allow(dead_code)]
        existing: TxHash,
    },
    /// The transactions fee_cap is lower than the chain's minimum fee requirement.
    /// 
    /// fee_cap is the transaction's max_fee_per_gas
    FeeCapBelowMinimumProtocolFeeCap { fee_cap: u128 },
    /// Sender currently exceeds the configured limit for max account slots.
    ///
    /// The sender can be considered a spammer at this point.
    ExceededSenderTransactionsCapacity { address: Address },
    /// Transaction gas limit exceeds block's gas limit
    TxGasLimitMoreThanAvailableBlockGas {
        block_gas_limit: u64,
        tx_gas_limit: u64,
    },
}
/// Transaction pool result type.
pub type PoolResult<T> = Result<T, PoolError>;


/// Transaction pool error
#[derive(Debug, thiserror::Error, Eq, PartialEq, Clone)]
#[error("[{hash}]: {kind}")]
pub struct PoolError {
    /// Hash of the transaction that caused the error
    pub hash: TxHash,
    /// The kind of error
    pub kind: PoolErrorKind
}

impl PoolError {
    pub fn new(hash: TxHash, kind: PoolErrorKind) -> Self {
        Self {
            hash,
            kind
        }
    }
}

/// The kind of pool error 
#[derive(Debug, thiserror::Error, Eq, PartialEq, Clone)]
pub enum PoolErrorKind {
    /// Transaction already exists in the pool
    #[error("already imported")]
    AlreadyImported,

    /// Currently the implementation only handles Eip1559 txs
    #[error("unknown transaction type")]
    UnknownTransactionType,

    /// On-chain nonce must be less than or equal to the transaction nonce
    #[error("invalid tx nonce: {0} > {1}")]
    InvalidTxNonce(u64, u64),

    /// Transaction signature error
    #[error("signature error for transaction")]
    SignatureError,

    /// Attempted to replace existing transaction, but was underpriced
    #[error("tried to replace existingtransaction with transaction but it was underpriced: {0}")]
    ReplacementUnderpriced(TxHash),

    /// The fee cap of the transaction is below the minimum fee cap determined by the protocol
    #[error("transaction feeCap below chain minimum for transaction: {0}")]
    FeeCapBelowMinimumProtocolFeeCap(u128),

    /// Sender currently exceeds the configured limit for max account slots.
    ///
    /// The sender can be considered a spammer at this point.
    #[error("sender {0} exceeds max account slots")]
    SpammerExceededCapacity(Address),

    /// Transaction gas limit exceeds block's gas limit
    #[error("transaction gas limit {1} exceeds block gas limit {0}")]
    TxGasLimitMoreThanAvailableBlockGas(u64, u64),
}