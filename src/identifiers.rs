
// -----identifiers.rs-----

use std::sync::Arc;

use alloy::{
    consensus::{TxEnvelope, Transaction},
    primitives::Address,
};


/// A unique identifier of a transaction of a Sender.
///
/// This serves as an identifier for dependencies of a transaction:
/// A transaction with a nonce higher than the current state nonce depends on `tx.nonce - 1`.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct TransactionId {
    /// Sender of this transaction
    pub sender: Address,
    /// Nonce of this transaction
    pub nonce: u64
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

impl From<Arc<TxEnvelope>> for TransactionId {
    fn from(tx: Arc<TxEnvelope>) -> Self {
        Self::new(tx.recover_signer().unwrap(), tx.nonce())
    }
}

// TODO: used?
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SenderTransactionCount {
    pub count: u64,
    pub last_submission_id: u64
}


#[cfg(test)]
mod tests {

    use super::*;
    use alloy::primitives::Address;

    #[test]
    fn test_ancestor() {
        let sender = Address::random();
        
        // Case: tx_nonce > on_chain_nonce
        assert_eq!(
            TransactionId::ancestor(5, 3, sender),
            Some(TransactionId::new(sender, 4))
        );

        // Case: tx_nonce <= on_chain_nonce
        assert_eq!(TransactionId::ancestor(3, 3, sender), None);
        assert_eq!(TransactionId::ancestor(2, 3, sender), None);
    }

    #[test]
    fn test_unchecked_ancestor() {
        let sender = Address::random();
        let tx_id = TransactionId::new(sender, 5);

        // Case: nonce > 0
        assert_eq!(
            tx_id.unchecked_ancestor(),
            Some(TransactionId::new(sender, 4))
        );

        // Case: nonce == 0
        let tx_id_zero = TransactionId::new(sender, 0);
        assert_eq!(tx_id_zero.unchecked_ancestor(), None);
    }

    #[test]
    fn test_descendant() {
        let sender = Address::random();
        let tx_id = TransactionId::new(sender, 5);

        assert_eq!(tx_id.descendant(), TransactionId::new(sender, 6));
    }

    #[test]
    fn test_next_nonce() {
        let sender = Address::random();
        let tx_id = TransactionId::new(sender, 5);

        assert_eq!(tx_id.next_nonce(), 6);
    }
}

