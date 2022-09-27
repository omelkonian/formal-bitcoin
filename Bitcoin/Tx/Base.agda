------------------------------------------------------------------------
-- Transactions.
------------------------------------------------------------------------
module Bitcoin.Tx.Base where

open import Prelude.Init
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
Witness n = Vec HashId n

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

∃i ∃o : ∃Tx → ℕ
∃i = proj₁
∃o = proj₁ ∘ proj₂

∃inputs : (tx : ∃Tx) → Vec TxInput (proj₁ tx)
∃inputs (_ , _ , tx) = inputs tx

∃outputs : (tx : ∃Tx) → Vec ∃TxOutput (proj₁ $ proj₂ tx)
∃outputs (_ , _ , tx) = outputs tx

Tx⁺ ⁺Tx ⁺Tx⁺ : ℕ → ℕ → Set
Tx⁺ i o = Tx i (suc o)
⁺Tx i o = Tx (suc i) o
⁺Tx⁺ i o = Tx (suc i) (suc o)

∃Tx⁺ = ∃[ i ] ∃[ o ] Tx⁺ i o
∃⁺Tx = ∃[ i ] ∃[ o ] ⁺Tx i o
∃⁺Tx⁺ = ∃[ i ] ∃[ o ] ⁺Tx⁺ i o

-- alternative representation of a transaction input, which is unhashed and well-bounded
record TxInput′ : Set where
  constructor _at_
  field
    tx′ : ∃Tx
    index′ : Fin (∃o tx′)
open TxInput′ public

variable
  i i′ o o′ : ℕ
  -- T T′ : ∃Tx

_‼ⁱ_ : Tx i o → Fin i → TxInput
tx ‼ⁱ i = V.lookup (inputs tx) i

_‼ʷ_ : Tx i o → Fin i → ∃Witness
tx ‼ʷ i = V.lookup (wit tx) i

_‼ʳ_ : Tx i o → Fin i → Time
tx ‼ʳ i = V.lookup (relLock tx) i

_‼ᵒ_ : Tx i o → Fin o → ∃TxOutput
tx ‼ᵒ i = V.lookup (outputs tx) i

-- Coinbase transactions start at time t=0.
-- Coinbase : Tx 0 o → Set
-- Coinbase tx = absLock tx ≡ 0

-- Timed transactions.
record TimedTx : Set where
  constructor _at_
  field
    transaction : ∃Tx
    time        : Time
open TimedTx public

unquoteDecl DecEqₜₜₓ = DERIVE DecEq [ quote TimedTx , DecEqₜₜₓ ]
