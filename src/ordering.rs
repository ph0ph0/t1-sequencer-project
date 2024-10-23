
// -----ordering.rs-----

use std::{fmt, marker::PhantomData};

use alloy::{
    consensus::{Transaction, TxEnvelope},
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