//! Transaction ordering and prioritization for the transaction pool.
//!
//! This module provides traits and implementations for ordering transactions
//! in the pool based on various criteria. It includes:
//!
//! - The `TransactionOrdering` trait for defining custom ordering strategies.
//! - The `Priority` enum for representing transaction priorities.
//! - The `CoinbaseTipOrdering` struct, which implements an ordering strategy
//!   based on the transaction's priority fee.
//!
//! These components allow for flexible and customizable transaction ordering
//! within the pool, enabling efficient management of pending transactions.

use std::{fmt, marker::PhantomData};

use alloy::{
    consensus::{Transaction, TxEnvelope},
    primitives::U256,
};

/// A trait for ordering transactions in the pool.
pub trait TransactionOrdering: Send + Sync + 'static {
    type PriorityValue: Ord + Clone + Default + fmt::Debug + Send + Sync;

    /// Returns the priority of the transaction.
    fn priority(&self, transaction: &TxEnvelope, base_fee: u64) -> Priority<Self::PriorityValue>;
}

/// A priority value for a transaction.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub enum Priority<T: Ord + Clone> {
    Value(T),
    None,
}

impl<T: Ord + Clone> From<Option<T>> for Priority<T> {
    /// Converts an `Option<T>` to a `Priority<T>`.
    fn from(value: Option<T>) -> Priority<T> {
        value.map_or(Self::None, Priority::Value)
    }
}

/// An ordering strategy that prioritizes transactions based on their priority fee.
#[derive(Debug, Eq, Ord, PartialEq, PartialOrd)]
#[non_exhaustive]
pub struct CoinbaseTipOrdering<T>(PhantomData<T>);

impl<T> TransactionOrdering for CoinbaseTipOrdering<T>
where
    T: Transaction + 'static,
{
    type PriorityValue = U256;

    /// Returns the priority of the transaction.
    fn priority(&self, transaction: &TxEnvelope, base_fee: u64) -> Priority<Self::PriorityValue> {
        // If the **effective** tip is zero, return Priority::None
        // effective tip = min(max_fee_per_gas - base_fee, max_priority_fee_per_gas)
        transaction
            .effective_tip_per_gas(base_fee)
            .map(U256::from)
            .and_then(|tip| if tip.is_zero() { None } else { Some(tip) })
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
    use alloy::primitives::U256;
    use crate::test_utils::helpers::create_tx_and_sender;

    #[tokio::test]
    async fn test_coinbase_tip_ordering_priority_with_default_fees() {
        let (tx, _, _) = create_tx_and_sender(100, 50, 1000, U256::from(0), 0).await;
        let ordering = CoinbaseTipOrdering::<TxEnvelope>::default();
        let base_fee = 40;

        // effective tip = min(max_fee_per_gas - base_fee, max_priority_fee_per_gas)
        // effective tx1_tip = min(100 - 40, 50) = 50
        let priority = ordering.priority(&tx, base_fee);
        let expected = U256::from(50);

        assert_eq!(
            priority,
            Priority::Value(expected),
            "Expected Priority::Value(50)"
        );
    }
    #[tokio::test]
    async fn test_coinbase_tip_ordering_zero_priority_fee() {
        let (tx, _, _) = create_tx_and_sender(100, 0, 1000, U256::from(0), 0).await;
        let ordering = CoinbaseTipOrdering::<TxEnvelope>::default();
        let base_fee = 40;

        let priority = ordering.priority(&tx, base_fee);

        assert_eq!(priority, Priority::None, "Expected Priority::None");
    }

    #[tokio::test]
    async fn test_coinbase_tip_ordering_max_priority_fee() {
        let (tx, _, _) = create_tx_and_sender(100, u128::MAX, 1000, U256::from(0), 0).await;
        let ordering = CoinbaseTipOrdering::<TxEnvelope>::default();
        let base_fee = 40;

        let priority = ordering.priority(&tx, base_fee);
        let expected = U256::from(60); // 100 - 40

        assert_eq!(
            priority,
            Priority::Value(expected),
            "Expected Priority::Value(60)"
        );
    }

    #[tokio::test]
    async fn test_coinbase_tip_ordering_base_fee_higher_than_max_fee() {
        let (tx, _, _) = create_tx_and_sender(100, 50, 1000, U256::from(0), 0).await;
        let ordering = CoinbaseTipOrdering::<TxEnvelope>::default();
        let base_fee = 110;

        let priority = ordering.priority(&tx, base_fee);

        assert_eq!(priority, Priority::None, "Expected Priority::None");
    }

    #[tokio::test]
    async fn test_coinbase_tip_ordering_base_fee_equal_to_max_fee() {
        let (tx, _, _) = create_tx_and_sender(100, 50, 1000, U256::from(0), 0).await;
        let ordering = CoinbaseTipOrdering::<TxEnvelope>::default();
        let base_fee = 100;

        let priority = ordering.priority(&tx, base_fee);

        assert_eq!(priority, Priority::None, "Expected Priority::None");
    }
}
