// -----sequence.rs-----

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::sync::Arc;

use tokio::sync::broadcast::{error::TryRecvError, Receiver};
use alloy::primitives::TxHash;
use alloy::consensus::{Transaction, TxEnvelope};

use crate::{
    ordering::TransactionOrdering,
    pool::pending::PendingTransaction,
    identifiers::TransactionId,
};

pub struct TransactionSequence<O>
where
    O: TransactionOrdering,
{
    /// Contains a copy of _all_ transactions of the pending pool at the point in time this
    /// iterator was created.
    pub(crate) all: BTreeMap<TransactionId, PendingTransaction<O>>,
    /// Transactions that can be executed right away: these have the expected nonce.
    ///
    /// Once an `independent` transaction with the nonce `N` is returned, it unlocks `N+1`, which
    /// then can be moved from the `all` set to the `independent` set.
    pub(crate) independent: BTreeSet<PendingTransaction<O>>,
    /// There might be the case where a yielded transactions is invalid, this will track it.
    pub(crate) invalid: HashSet<TxHash>,
}

impl<O: TransactionOrdering> TransactionSequence<O> {
    /// Mark the transaction and it's descendants as invalid.
    pub(crate) fn mark_invalid(&mut self, tx: &Arc<TxEnvelope>) {
        self.invalid.insert(*tx.tx_hash());
    }

    /// Returns the ancestor the given transaction, the transaction with `nonce - 1`.
    ///
    /// Note: for a transaction with nonce higher than the current on chain nonce this will always
    /// return an ancestor since all transaction in this pool are gapless.
    pub(crate) fn ancestor(&self, id: &TransactionId) -> Option<&PendingTransaction<O>> {
        self.all.get(&id.unchecked_ancestor()?)
    }
}

impl<O: TransactionOrdering> Default for TransactionSequence<O> {
    fn default() -> Self {
        Self {
            all: BTreeMap::new(),
            independent: BTreeSet::new(),
            invalid: HashSet::new(),
        }
    }
}


impl<O: TransactionOrdering> Iterator for TransactionSequence<O> {
    type Item = Arc<PendingTransaction<O>>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // Remove the next independent tx with the highest priority
            let best = self.independent.pop_last()?;
            let hash = best.transaction().tx_hash();

            // skip transactions that were marked as invalid
            if self.invalid.contains(hash) {
                println!(
                    "[{:?}] skipping invalid transaction",
                    hash
                );
                continue
            }

            // Insert transactions that just got unlocked.
            if let Some(unlocked) = self.all.get(&best.unlocks()) {
                self.independent.insert(unlocked.clone());
            }
            return Some(Arc::new(best));
        }
    }
}

/// A[`TransactionSequence`] implementation that filters the
/// transactions of iter with predicate.
///
/// Filter out transactions are marked as invalid:
/// [`TransactionSequence::mark_invalid`]
pub struct TransactionSequenceFilter<O, P>
where
    O: TransactionOrdering,
{
    pub(crate) transaction_sequence: TransactionSequence<O>,
    pub(crate) predicate: P,
}

impl<O, P> TransactionSequenceFilter<O, P>
where
    O: TransactionOrdering,
{
    /// Create a new [`TransactionSequenceFilter`] with the given predicate.
    pub(crate) const fn new(transaction_sequence: TransactionSequence<O>, predicate: P) -> Self {
        Self { transaction_sequence, predicate }
    }
}

impl<O, P> Iterator for TransactionSequenceFilter<O, P>
where
    O: TransactionOrdering,
    P: FnMut(&<TransactionSequence<O> as Iterator>::Item) -> bool,
{
    type Item = <TransactionSequence<O> as Iterator>::Item;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let best = self.transaction_sequence.next()?;
            if (self.predicate)(&best) {
                return Some(best)
            }
            self.transaction_sequence.mark_invalid(&best.transaction());
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use alloy::primitives::Address;
    use crate::ordering::{CoinbaseTipOrdering, Priority};
    use crate::pool::pending::PendingTransaction;
    use alloy::consensus::TxEnvelope;
    use std::sync::Arc;
    use alloy::primitives::U256;
    use crate::test_utils::helpers::{create_default_tx_and_sender, create_tx, create_tx_and_sender};

    #[tokio::test]
    async fn test_mark_invalid() {
        let mut sequence = TransactionSequence::<CoinbaseTipOrdering<TxEnvelope>>::default();
        
        // Create a mock transaction
        let (tx, sender, _) = create_default_tx_and_sender().await;
        let base_fee = 5;
        let priority: Priority<U256> = CoinbaseTipOrdering::<TxEnvelope>::default().priority(&tx, base_fee);
        let pending_tx: PendingTransaction<CoinbaseTipOrdering<TxEnvelope>> = PendingTransaction::new(
            0,
            Arc::clone(&tx),
            priority,
            sender,
        );

        // Mark the transaction as invalid
        sequence.mark_invalid(&tx);

        // Check that the transaction is in the invalid set
        assert!(sequence.invalid.contains(tx.tx_hash()));
    }

    #[tokio::test]
    async fn test_ancestor() {
        let mut sequence = TransactionSequence::<CoinbaseTipOrdering<TxEnvelope>>::default();
        // Create two transactions with consecutive nonces
        let (tx1, sender, private_key) = create_default_tx_and_sender().await;
        let tx2 = create_tx(private_key, sender, 15, 25, 100000, U256::ZERO, 1).await;

        let base_fee = 10;
        let ordering = CoinbaseTipOrdering::<TxEnvelope>::default();

        // Add transactions to the sequence
        sequence.all.insert(
            TransactionId::new(sender, 0),
            PendingTransaction::new(
                0,
                Arc::clone(&tx1),
                ordering.priority(&tx1, base_fee),
                sender,
            ),
        );
        sequence.all.insert(
            TransactionId::new(sender, 1),
            PendingTransaction::new(
                1,
            Arc::clone(&tx2),
            ordering.priority(&tx2, base_fee),
                sender,
            ),
        );

        let tx1_id = TransactionId::new(sender, 0);
        let tx2_id = TransactionId::new(sender, 1);

        // Check ancestor
        assert!(sequence.ancestor(&tx2_id).is_some());
        assert_eq!(sequence.ancestor(&tx2_id).unwrap().transaction().nonce(), 0);
        
        // Check that tx1 has no ancestor
        assert!(sequence.ancestor(&tx1_id).is_none());
    }

    #[tokio::test]
    async fn test_transaction_sequence_iterator() {
        // Tests that the transaction sequence iterator returns transactions in the correct order
        // and skips invalid transactions.

        // Create the TransactionSequence
        let mut sequence = TransactionSequence::<CoinbaseTipOrdering<TxEnvelope>>::default();

        // Create three transactions with consecutive nonces
        let (tx1, sender, private_key) = create_default_tx_and_sender().await;
        let tx2 = create_tx(private_key.clone(), sender, 15, 25, 100000, U256::ZERO, 1).await;
        let tx3 = create_tx(private_key, sender, 20, 30, 100000, U256::ZERO, 2).await;

        // Create the ordering and base fee
        let base_fee = 10;
        let ordering = CoinbaseTipOrdering::<TxEnvelope>::default();

        // Add transactions to the sequence
        sequence.all.insert(
            TransactionId::new(sender, 0),
            PendingTransaction::new(
                0,
                Arc::clone(&tx1),
                ordering.priority(&tx1, base_fee),
                sender,
            ),
        );
        sequence.all.insert(
            TransactionId::new(sender, 1),
            PendingTransaction::new(
                1,
                Arc::clone(&tx2),
                ordering.priority(&tx2, base_fee),
                sender,
            ),
        );
        sequence.all.insert(
            TransactionId::new(sender, 2),
            PendingTransaction::new(
                2,
                Arc::clone(&tx3),
                ordering.priority(&tx3, base_fee),
                sender,
            ),
        );

        // Add transactions to the independent set
        sequence.independent.insert(sequence.all.get(&TransactionId::new(sender, 0)).unwrap().clone());

        // First transaction
        let next_tx = sequence.next().unwrap();
        assert_eq!(next_tx.transaction().nonce(), 0);

        // Second transaction (unlocked by the first)
        let next_tx = sequence.next().unwrap();
        assert_eq!(next_tx.transaction().nonce(), 1);

        // Third transaction (unlocked by the second)
        let next_tx = sequence.next().unwrap();
        assert_eq!(next_tx.transaction().nonce(), 2);

        // No more transactions
        assert!(sequence.next().is_none());

        // Test with an invalid transaction
        sequence = TransactionSequence::<CoinbaseTipOrdering<TxEnvelope>>::default();
        sequence.all.insert(
            TransactionId::new(sender, 0),
            PendingTransaction::new(
                0,
                Arc::clone(&tx1),
                ordering.priority(&tx1, base_fee),
                sender,
            ),
        );
        sequence.independent.insert(sequence.all.get(&TransactionId::new(sender, 0)).unwrap().clone());
        sequence.invalid.insert(*tx1.tx_hash());

        assert!(sequence.next().is_none());
    }

    #[tokio::test]
    async fn test_invalid_transaction_descendants() {
        // Tests that the transaction sequence iterator skips the descendants of invalid transactions.

        // Create the TransactionSequence
        let mut sequence = TransactionSequence::<CoinbaseTipOrdering<TxEnvelope>>::default();
        let ordering = CoinbaseTipOrdering::<TxEnvelope>::default();
        let base_fee = 10;

        // Create transactions
        let (tx1, sender, private_key) = create_default_tx_and_sender().await;
        let tx2 = create_tx(private_key.clone(), sender, 15, 25, 100000, U256::ZERO, 1).await;
        let tx3 = create_tx(private_key.clone(), sender, 20, 30, 100000, U256::ZERO, 2).await;

        // Add transactions to the sequence
        sequence.all.insert(
            TransactionId::new(sender, 0),
            PendingTransaction::new(
                0,
                Arc::clone(&tx1),
                ordering.priority(&tx1, base_fee),
                sender,
            ),
        );
        sequence.all.insert(
            TransactionId::new(sender, 1),
            PendingTransaction::new(
                1,
                Arc::clone(&tx2),
                ordering.priority(&tx2, base_fee),
                sender,
            ),
        );
        sequence.all.insert(
            TransactionId::new(sender, 2),
            PendingTransaction::new(
                2,
                Arc::clone(&tx3),
                ordering.priority(&tx3, base_fee),
                sender,
            ),
        );

        // Add the first transaction to the independent set
        sequence.independent.insert(sequence.all.get(&TransactionId::new(sender, 0)).unwrap().clone());

        // Mark the second transaction as invalid
        sequence.mark_invalid(&tx2);

        // First transaction should be returned
        let next_tx = sequence.next().unwrap();
        assert_eq!(next_tx.transaction().nonce(), 0);

        // No more transactions should be returned
        assert!(sequence.next().is_none());
    }

    #[tokio::test]
    async fn test_transaction_sequence_filter() {
        let ordering = CoinbaseTipOrdering::<TxEnvelope>::default();
        let mut sequence = TransactionSequence::default();
        let base_fee = 10;

        // Create transactions
        let (tx1, sender, private_key) = create_default_tx_and_sender().await;
        let tx2 = create_tx(private_key.clone(), sender, 15, 25, 100000, U256::ZERO, 1).await;
        let tx3 = create_tx(private_key.clone(), sender, 20, 30, 100000, U256::ZERO, 2).await;

        // Add transactions to the sequence
        sequence.all.insert(
            TransactionId::new(sender, 0),
            PendingTransaction::new(
                0,
                Arc::clone(&tx1),
                ordering.priority(&tx1, base_fee),
                sender,
            ),
        );
        sequence.all.insert(
            TransactionId::new(sender, 1),
            PendingTransaction::new(
                1,
                Arc::clone(&tx2),
                ordering.priority(&tx2, base_fee),
                sender,
            ),
        );
        sequence.all.insert(
            TransactionId::new(sender, 2),
            PendingTransaction::new(
                2,
                Arc::clone(&tx3),
                ordering.priority(&tx3, base_fee),
                sender,
            ),
        );

        // Add transaction 1 to the independent set
        sequence.independent.insert(sequence.all.get(&TransactionId::new(sender, 0)).unwrap().clone());

        // Create a filter that only accepts transactions with even nonces
        let predicate = |tx: &Arc<PendingTransaction<CoinbaseTipOrdering<TxEnvelope>>>| {
            tx.transaction().nonce() % 2 == 0
        };

        let mut filter = TransactionSequenceFilter::new(sequence, predicate);

        // First transaction should be returned (nonce 0)
        let next_tx = filter.next().unwrap();
        assert_eq!(next_tx.transaction().nonce(), 0);

        // Third transaction should be returned (nonce 2)
        let next_tx = filter.next().unwrap();
        assert_eq!(next_tx.transaction().nonce(), 2);

        // No more transactions should be returned
        assert!(filter.next().is_none());
    }
}

