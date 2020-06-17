------------------------------------------------------------------------
-- Transactions.
------------------------------------------------------------------------
module Bitcoin.Tx.Base where

open import Data.Nat     using (ℕ)
open import Data.Product using (∃-syntax; _,_)
open import Data.Fin     using (Fin)
open import Data.Integer using (ℤ)
open import Data.Vec     using (Vec; lookup)

open import Relation.Binary.PropositionalEquality using (_≡_)

open import Prelude.Lists
open import Prelude.DecEq

open import Bitcoin.BasicTypes
open import Bitcoin.Script.Base

record TxInput : Set where
  constructor _at_
  field
    txId  : HashId  -- referenced previous transaction
    index : ℕ       -- index in the referenced transaction's outputs
open TxInput public
unquoteDecl DecEqᵢ = DERIVE DecEq [ quote TxInput , DecEqᵢ ]

record TxOutput (ctx : ScriptContext) : Set where
  field
    value     : Value
    validator : BitcoinScript ctx
open TxOutput public
unquoteDecl DecEqₒ = DERIVE DecEq [ quote TxOutput , DecEqₒ ]
∃TxOutput = ∃[ ctx ] TxOutput ctx

Witness : ℕ → Set
Witness n = Vec ℤ n

∃Witness = ∃[ n ] Witness n

record Tx (i o : ℕ) : Set where
  field
    inputs  : Vec TxInput  i   -- inputs
    wit     : Vec ∃Witness i   -- segragated witnesses
    relLock : Vec Time     i   -- relative timelocks

    outputs : Vec ∃TxOutput o  -- outputs
    absLock : Time             -- absolute timelock
open Tx public

unquoteDecl DecEqₜₓ = DERIVE DecEq [ quote Tx , DecEqₜₓ ]

∃Tx = ∃[ i ] ∃[ o ] Tx i o

variable
  i i′ o o′ : ℕ

_‼ⁱ_ : Tx i o → Fin i → TxInput
tx ‼ⁱ i = lookup (inputs tx) i

_‼ʷ_ : Tx i o → Fin i → ∃Witness
tx ‼ʷ i = lookup (wit tx) i

_‼ʳ_ : Tx i o → Fin i → Time
tx ‼ʳ i = lookup (relLock tx) i

_‼ᵒ_ : Tx i o → Fin o → ∃TxOutput
tx ‼ᵒ i = lookup (outputs tx) i

-- Coinbase transactions start at time t=0.
Coinbase : Tx 0 o → Set
Coinbase tx = absLock tx ≡ 0

-- Timed transactions.
record TimedTx : Set where
  constructor _at_
  field
    transaction : ∃Tx
    time        : Time
open TimedTx public

unquoteDecl DecEqₜₜₓ = DERIVE DecEq [ quote TimedTx , DecEqₜₜₓ ]
