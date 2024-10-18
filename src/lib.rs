// -----sequence.rs-----

use std::collections::{BTreeSet, BTreeMap, HashMap};
use std::cmp::{Ordering};
use alloy::primitives::Address;
use std::sync::Arc;


#[derive(PartialOrd, Eq, PartialEq)]
pub struct PendingTransaction<T, O>
where
    T: Transaction + PartialEq + Eq + PartialOrd + Ord,
    O: TransactionOrdering<T> + PartialEq + Eq + PartialOrd + Ord,
{
    submission_id: u64,
    transaction: Box<T>,
    priority: Priority<O::PriorityValue>,
    // alloy Transaction type doesn't contain a sender field, so we must extract it from the TxEnvelope
    sender: Address
}

impl<T, O> Ord for PendingTransaction<T, O> 
where
    T: Transaction + PartialEq + Eq + PartialOrd + Ord,
    O: TransactionOrdering<T> + PartialEq + Eq + PartialOrd + Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        // Primary sort by priority fee (descending)
        other.priority.cmp(&self.priority)
            // Secondary sort by address
            .then(self.sender.cmp(&other.sender))
            // Tertiary sort by nonce
            .then(self.transaction.nonce().cmp(&other.transaction.nonce()))
    }
}

pub struct TransactionSequence<T, O>
where
    T: Transaction + PartialEq + Eq + PartialOrd + Ord,
    O: TransactionOrdering<T> + PartialEq + Eq + PartialOrd + Ord,
{
    ordering: O,
    sequenced_transactions: BTreeSet<PendingTransaction<T, O>>,
    // nonce_map: HashMap<u64, u64>, //TODO: Remove
    sum_priority_fee: u128,
}

// ------pool.rs-----


pub struct Pool <T, O>
where
    T: Transaction + PartialEq + Eq + PartialOrd + Ord,
    O: TransactionOrdering<T> + PartialEq + Eq + PartialOrd + Ord,
{
    /// All transactions in the pool, grouped by sender, ordered by nonce
    all_transactions: BTreeMap<TransactionId, Arc<dyn Transaction>>,
    /// Struct that holds transactions ordered by priority fee and respects nonce ordering
    transaction_sequence: TransactionSequence<T, O>
}

// -----identifiers.rs-----

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

// -----ordering.rs-----

use std::{fmt, marker::PhantomData};
use alloy::{
    consensus::Transaction,
    primitives::U256
};

pub trait TransactionOrdering<T: Transaction>: Send + Sync + 'static {
    
    type PriorityValue: Ord + Clone + Default + fmt::Debug + Send + Sync;

    fn priority(
        &self,
        transaction: &T,
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

impl<T> TransactionOrdering<T> for CoinbaseTipOrdering<T> 
where   
    T: Transaction + 'static,
{
    
    type PriorityValue = U256;

    fn priority(
        &self,
        transaction: &T,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_coinbase_tip_ordering_priority_with_default_fees() {
        // Scenario: max_fee_priority_fee_per_gas == MockTransaction default value
        // Expect: Priority::Value(expected)
        let tx = MockTransaction::eip1559();
        let ordering: CoinbaseTipOrdering<MockTransaction> = CoinbaseTipOrdering::default();
        let base_fee = 3;

        let priority = ordering.priority(&tx, base_fee);
        let expected = U256::from(tx.get_max_fee().unwrap() as u64 - base_fee);

        assert_eq!(priority, Priority::Value(expected), "Expected Priority::Value");
    }

    #[test]
    fn test_coinbase_tip_ordering_zero_priority_fee() {
        // Scenario: max_fee_priority_fee_per_gas == 0
        // Expect: Priority::None since the **effective** tip is calculated (ie tip = min(max_fee - base_fee, max_priority_fee)) 
        let tx = MockTransaction::eip1559().with_priority_fee(0);
        let ordering: CoinbaseTipOrdering<MockTransaction> = CoinbaseTipOrdering::default();
        let base_fee = 3;

        let priority = ordering.priority(&tx, base_fee);

        assert_eq!(Priority::None, priority, "Expected Priority::None, got Priority::Value");
    }

    #[test]
    fn test_coinbase_tip_ordering_max_priority_fee() {
        // Scenario: max_fee_priority_fee_per_gas == u128::MAX
        // Expect: Priority::Value(max_fee - base_fee) 
        let tx = MockTransaction::eip1559().with_priority_fee(u128::MAX);
        let ordering: CoinbaseTipOrdering<MockTransaction> = CoinbaseTipOrdering::default();
        let base_fee = 1;

        let priority = ordering.priority(&tx, base_fee);
        let expected = U256::from(tx.get_max_fee().unwrap() as u64 - base_fee);

        assert_eq!(priority, Priority::Value(expected), "Expected Priority::Value");
    }

    #[test]
    fn test_coinbase_tip_ordering_base_fee_higher_than_max_fee() {
        // Scenario: base_fee > max_fee_per_gas
        // Expect: Priority::None since the **effective** tip is calculated (ie tip = min(max_fee - base_fee, max_priority_fee)) 
        let tx = MockTransaction::eip1559().with_max_fee(0);
        let ordering: CoinbaseTipOrdering<MockTransaction> = CoinbaseTipOrdering::default();
        let base_fee = 3;

        let priority = ordering.priority(&tx, base_fee);
        assert!(matches!(priority, Priority::None), "Expected Priority::None");
    }

    #[test]
    fn test_coinbase_tip_ordering_max_fee() {
        // Scenario: max_fee_priority_fee_per_gas == u128::MAX
        // Expect: Priority::Value(max_fee - base_fee) 
        let tx = MockTransaction::eip1559().with_max_fee(u128::MAX);
        let ordering: CoinbaseTipOrdering<MockTransaction> = CoinbaseTipOrdering::default();
        let base_fee = 1;

        let priority = ordering.priority(&tx, base_fee);
        let expected = U256::from(tx.get_priority_fee().unwrap());

        assert_eq!(priority, Priority::Value(expected), "Expected Priority::Value");
    }
}

// -----test_utils/mock.rs-----

use alloy::consensus::{
    //Transaction,
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