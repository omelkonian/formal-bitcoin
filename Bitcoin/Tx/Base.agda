------------------------------------------------------------------------
-- Transactions.
------------------------------------------------------------------------
module Bitcoin.Tx.Base where

open import Prelude.Init; open SetAsType
open import Prelude.Lists
open import Prelude.DecEq

open import Bitcoin.BasicTypes
open import Bitcoin.Script.Base

record TxInput : Type where
  constructor _at_
  field txId  : HashId  -- referenced previous transaction
        index : ℕ       -- index in the referenced transaction's outputs
open TxInput public
unquoteDecl DecEqᵢ = DERIVE DecEq [ quote TxInput , DecEqᵢ ]

infix 5 _locked-by_
record TxOutput (ctx : ScriptContext) : Type where
  constructor _locked-by_
  field value     : Value
        validator : BitcoinScript ctx
open TxOutput public
unquoteDecl DecEqₒ = DERIVE DecEq [ quote TxOutput , DecEqₒ ]
∃TxOutput = ∃[ ctx ] TxOutput ctx

Witness : ℕ → Type
Witness n = Vec HashId n

∃Witness = ∃[ n ] Witness n

record Tx (i o : ℕ) : Type where
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
∃inputs (_ , _ , tx) = tx .inputs

∃outputs : (tx : ∃Tx) → Vec ∃TxOutput (proj₁ $ proj₂ tx)
∃outputs (_ , _ , tx) = tx .outputs

Tx⁺ ⁺Tx ⁺Tx⁺ : ℕ → ℕ → Type
Tx⁺ i o = Tx i (suc o)
⁺Tx i o = Tx (suc i) o
⁺Tx⁺ i o = Tx (suc i) (suc o)

∃Tx⁺ = ∃[ i ] ∃[ o ] Tx⁺ i o
∃⁺Tx = ∃[ i ] ∃[ o ] ⁺Tx i o
∃⁺Tx⁺ = ∃[ i ] ∃[ o ] ⁺Tx⁺ i o

-- alternative representation of a transaction input, which is unhashed and well-bounded
record TxInput′ : Type where
  constructor _at_
  field tx′    : ∃Tx
        index′ : Fin (∃o tx′)
open TxInput′ public
unquoteDecl DecEqₜₓᵢ = DERIVE DecEq [ quote TxInput′ , DecEqₜₓᵢ ]

variable
  i i′ o o′ : ℕ
  -- T T′ : ∃Tx

_‼ⁱ_ : Tx i o → Fin i → TxInput
_‼ⁱ_ = V.lookup ∘ inputs

_‼ʷ_ : Tx i o → Fin i → ∃Witness
_‼ʷ_ = V.lookup ∘ wit

_‼ʳ_ : Tx i o → Fin i → Time
_‼ʳ_ = V.lookup ∘ relLock

_‼ᵒ_ : Tx i o → Fin o → ∃TxOutput
_‼ᵒ_ = V.lookup ∘ outputs

-- Coinbase transactions start at time t=0.
-- Coinbase : Tx 0 o → Type
-- Coinbase tx = absLock tx ≡ 0

-- Timed transactions.
record TimedTx : Type where
  constructor _at_
  field transaction : ∃Tx
        time        : Time
open TimedTx public

unquoteDecl DecEqₜₜₓ = DERIVE DecEq [ quote TimedTx , DecEqₜₜₓ ]

-- Accessors.
open import Prelude.Accessors

-- Value accessor.

unquoteDecl _∙Value _∙value ∙value=_ =
  genAccessor _∙Value _∙value ∙value=_ (quote Value)
instance
  TxOutput∙Value : TxOutput ctx ∙Value
  TxOutput∙Value = ∙value= value

  ∃TxOutput∙Value : ∃TxOutput ∙Value
  ∃TxOutput∙Value = ∙value= λ (_ , txo) → txo ∙value

  TxInput′∙Value : TxInput′ ∙Value
  TxInput′∙Value = ∙value= λ ((_ , _ , T) at o) → (T ‼ᵒ o) ∙value

-- Context accessor.

open import Prelude.Newtype
≫ScriptContext = newtype ScriptContext

∙ctx=_ : ∀ {A : Type} → (A → ScriptContext) → HasField A _
∙ctx= f = λ where ._∙ x → mk (f x)

_∙ctx : ∀ {A : Type} → ⦃ HasField A _ ⦄ → (A → ScriptContext)
_∙ctx = unmk ∘ _∙

instance
  Script∙Ctx : HasField (BitcoinScript ctx) ≫ScriptContext
  Script∙Ctx {ctx = ctx} = ∙ctx= const ctx

  TxOutput∙Ctx : HasField (TxOutput ctx) ≫ScriptContext
  TxOutput∙Ctx {ctx = ctx} = ∙ctx= const ctx

  ∃TxOutput∙Ctx : HasField ∃TxOutput ≫ScriptContext
  ∃TxOutput∙Ctx = ∙ctx= λ (_ , txo) → txo ∙ctx

  TxInput′∙Ctx : HasField TxInput′ ≫ScriptContext
  TxInput′∙Ctx = ∙ctx= λ ((_ , _ , T) at o) → (T ‼ᵒ o) ∙ctx

-- Validator accessor.

_∙validator : ∀ {A : Type} ⦃ _ : HasField A ≫ScriptContext ⦄
            → ⦃ HasField′ A _ ⦄
            → ∀ (a : A) → BitcoinScript (a ∙ctx)
_∙validator = _∙

instance
  TxOutput∙Validator : HasField (TxOutput ctx) (BitcoinScript ctx)
  TxOutput∙Validator ._∙ = validator

  ∃TxOutput∙Validator : HasField′ ∃TxOutput (BitcoinScript ∘ _∙ctx)
  ∃TxOutput∙Validator ._∙ (_ , txo) = txo ∙validator

  TxInput′∙Validator : HasField′ TxInput′ (BitcoinScript ∘ _∙ctx)
  TxInput′∙Validator ._∙ ((_ , _ , T) at o) = (T ‼ᵒ o) ∙validator
