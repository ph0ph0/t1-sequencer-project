pub mod helpers;

// // -----test_utils/mock.rs-----

// use alloy::consensus::{
//     //Transaction,
//     // TxEnvelope,
//     TxType
// };
// use alloy::primitives::{
//     B256, 
//     // Address, 
//     ChainId, 
//     // U256, 
//     TxKind, 
//     Bytes,
//     FixedBytes
// };
// use alloy::eips::{
//     eip2930::AccessList,
//     eip7702::SignedAuthorization,
// };

// /// A Bare transaction type used for testing.
// #[derive(Debug, Clone, Eq, PartialEq)]
// pub enum MockTransaction {
//     /// Eip1559 transaction type
//     Eip1559 {
//         /// The chain id of the transaction
//         chain_id: ChainId,
//         /// The hash of the transaction
//         hash: B256, 
//         /// The sender's address
//         sender: Address,
//         /// The transaction nonce
//         nonce: u64,
//         /// The maximum fee per gas for the transaction
//         max_fee_per_gas: u128,
//         /// The maximum priority fee per gas for the transaction
//         max_priority_fee_per_gas: u128,
//         /// The gas limit for the transaction
//         gas_limit: u64,
//         /// The transaction's destination address
//         to: TxKind,
//         /// The value of the transaction
//         value: U256,
//         /// The access list for the transaction
//         access_list: AccessList,
//         /// The transaction input data
//         input: Bytes,        
//     }
// }

// impl MockTransaction {
//     pub fn eip1559() -> Self {
//         Self::Eip1559{
//             chain_id: 1,
//             hash: B256::random(),
//             sender: Address::random(),
//             nonce: 0,
//             max_fee_per_gas: 7,
//             max_priority_fee_per_gas: 4,
//             gas_limit: 0,
//             to: Address::random().into(),
//             value: Default::default(),
//             input: Bytes::new(),
//             access_list: Default::default(),
//         }
//     }

//     pub fn set_priority_fee(&mut self, val: u128) -> &mut Self {
//         match self {
//             Self::Eip1559 { max_priority_fee_per_gas, .. } => {
//                 *max_priority_fee_per_gas = val;
//             }
//         }
//         self
//     }

//     pub fn with_priority_fee(mut self, val: u128) -> Self{
//         self.set_priority_fee(val);
//         self
//     }

//     pub const fn get_priority_fee(&self) -> Option<u128> {
//         match self {
//             Self::Eip1559 { max_priority_fee_per_gas, .. } => Some(*max_priority_fee_per_gas),
//         }
//     }

//     pub fn set_max_fee(&mut self, val: u128) -> &mut Self {
//         match self {
//             Self::Eip1559 { max_fee_per_gas, .. } => {
//                 *max_fee_per_gas = val;
//             }
//         }
//         self
//     }
    
//     pub fn with_max_fee(mut self, val: u128) -> Self {
//         self.set_max_fee(val);
//         self
//     }

//     pub const fn get_max_fee(&self) -> Option<u128> {
//         match self {
//             Self::Eip1559 { max_fee_per_gas, .. } => Some(*max_fee_per_gas),
//         }
//     }

//     /// Simultaneously sets the max fee and max priority fee to the same value for convenience
//     pub fn set_gas_price(&mut self, val: u128) -> &mut Self {
//         match self {
//             Self::Eip1559 { max_fee_per_gas, max_priority_fee_per_gas, .. } => {    
//                 *max_fee_per_gas = *max_priority_fee_per_gas;
//                 *max_priority_fee_per_gas = val;
//             }
//         }
//         self
//     }

//     /// Simultaneously sets the max fee and max priority fee to the same value for convenience
//     pub fn with_gas_price(mut self, val: u128) -> Self {
//         match self {
//             Self::Eip1559 { ref mut max_fee_per_gas, ref mut max_priority_fee_per_gas, .. } => {
//                 *max_fee_per_gas = val;
//                 *max_priority_fee_per_gas = val;
//             }
//         }
//         self
//     }
    
//     pub const fn get_gas_price(&self) -> u128 {
//         match self {
//             Self::Eip1559 { max_fee_per_gas, .. } => *max_fee_per_gas,
//         }
//     }

//     pub fn set_hash(&mut self, val: B256) -> &mut Self {
//         match self {
//             Self::Eip1559 { hash, .. } => *hash = val,
//         }
//         self
//     }

//     pub fn with_hash(mut self, val: B256) -> Self {
//         self.set_hash(val);
//         self
//     }

//     pub const fn get_hash(&self) -> B256 {
//         match self {
//             Self::Eip1559 { hash, .. } => *hash,
//         }
//     }

//     pub fn set_nonce(&mut self, val: u64) -> &mut Self {
//         match self {
//             Self::Eip1559 { nonce, .. } => *nonce = val,
//         }
//         self
//     }

//     pub fn with_nonce(mut self, val: u64) -> Self {
//         self.set_nonce(val);
//         self
//     }

//     pub const fn get_nonce(&self) -> u64 {
//         match self {
//             Self::Eip1559 { nonce, .. } => *nonce,
//         }
//     }
    
//     /// Returns a clone of the transaction with a new hash and nonce decremented by one
//     pub fn prev(&self) -> Self {
//         self.clone().with_hash(B256::random()).with_nonce(self.get_nonce() - 1) 
//     }

//     /// Returns a clone of the transaction with a new hash and nonce incremented by one
//     pub fn next(&self) -> Self {
//         self.clone().with_hash(B256::random()).with_nonce(self.get_nonce() + 1)
//     }

//     /// Returns a clone of the transaction with a new hash and nonce incremented by `n`
//     pub fn skip(&self, n: u64) -> Self {
//         self.clone().with_hash(B256::random()).with_nonce(self.get_nonce() + n)
//     }

//     /// Returns a clone of the transaction with a new hash and max priority fee incremented by `n`
//     pub fn inc_price_by(&self, n: u128) -> Self {
//         self.clone().with_hash(B256::random()).with_priority_fee(self.get_priority_fee().unwrap() + n)
//     }

//     /// Returns a clone of the transaction with a new hash and max priority fee incremented by one
//     pub fn inc_price(&self) -> Self {
//         self.clone().inc_price_by(1)
//     }

//     /// Returns a clone of the transaction with a new hash and max priority fee decremented by `n`
//     pub fn dec_price_by(&self, n: u128) -> Self {
//         self.clone().with_hash(B256::random()).with_priority_fee(self.get_priority_fee().unwrap() - n)
//     }

//     /// Returns a clone of the transaction with a new hash and max priority fee decremented by one
//     pub fn dec_price(&self) -> Self {
//         self.clone().dec_price_by(1)
//     }

// }

// // Match statements are used so that the implementation can be extended to other transaction types in the future
// impl Transaction for MockTransaction {
//     fn chain_id(&self) -> Option<u64> {
//         match self {
//             MockTransaction::Eip1559 { chain_id, .. } => Some(*chain_id),
//         }
//     }

//     fn nonce(&self) -> u64 {
//         match self {
//             MockTransaction::Eip1559 {nonce, ..} => *nonce,
//         }
//     }

//     fn gas_limit(&self) -> u64 {
//         match self {
//             MockTransaction::Eip1559 {gas_limit, ..} => *gas_limit,
//         }
//     }

//     fn gas_price(&self) -> Option<u128> {
//         match self {
//             MockTransaction::Eip1559 {..} => None,
//         }
//     }

//     fn max_fee_per_gas(&self) ->u128 {
//         match self {
//             MockTransaction::Eip1559 {max_fee_per_gas, ..} => *max_fee_per_gas,
//         }
//     }

//     fn max_priority_fee_per_gas(&self) -> Option<u128> {
//         match self {
//             MockTransaction::Eip1559 {max_priority_fee_per_gas, ..} => Some(*max_priority_fee_per_gas),
//         }
//     }
    
//     fn max_fee_per_blob_gas(&self) -> Option<u128> {
//         match self {
//             MockTransaction::Eip1559 {..} => None,
//         }
//     }

//     fn priority_fee_or_price(&self) -> u128 {
//         match self {
//             MockTransaction::Eip1559 {max_priority_fee_per_gas, ..} => *max_priority_fee_per_gas,
//         }
//     }

//     fn to(&self) -> TxKind {
//         match self {
//             MockTransaction::Eip1559 {to, ..} => *to,
//         }
//     }

//     fn value(&self) -> U256 {
//         match self {
//             MockTransaction::Eip1559 {value, ..} => *value,
//         }
//     }

//     fn input(&self) -> &[u8] {
//         match self {
//             MockTransaction::Eip1559 {input, ..} => input,
//         }
//     }
    
//     fn ty(&self) -> u8 {
//         match self {
//             MockTransaction::Eip1559 {..} => TxType::Eip1559 as u8,
//         }
//     }

//     fn access_list(&self) -> Option<&AccessList> {
//         match self {
//             MockTransaction::Eip1559 {access_list, ..} => Some(access_list),
//         }
//     }

//     fn blob_versioned_hashes(&self) -> Option<&[FixedBytes<32>]> {
//         match self {
//             MockTransaction::Eip1559 {..} => None,
//         }
//     }

//     fn authorization_list(&self) -> Option<&[SignedAuthorization]> {
//         match self {
//             MockTransaction::Eip1559 {..} => None,
//         }
//     }
// }