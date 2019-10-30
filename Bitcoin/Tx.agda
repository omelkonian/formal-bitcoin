------------------------------------------------------------------------
-- Transactions and ledgers.
------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}
module Bitcoin.Tx where

open import Function      using (_∘_; _$_)
open import Data.Bool     using (Bool; true; false; T; if_then_else_)
open import Data.Nat      using (ℕ; suc; _≟_; _≤_; s≤s; z≤n; _≥?_)
open import Data.Product  using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Maybe    using (Maybe; just; nothing; fromMaybe)
open import Data.Fin as F using (Fin; toℕ)
  renaming (zero to 0F)
open import Data.Integer  using (ℤ; +_; _+_; _-_; _<_; _<?_)
  renaming (_≟_ to _≟ℤ_)

open import Data.List           using (List; []; _∷_; map)
open import Data.Vec as V       using (Vec; lookup; _[_]≔_)
open import Data.Vec.Properties using (≡-dec)

open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Nullary.Decidable            using (⌊_⌋)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Bitcoin.BasicTypes
open import Bitcoin.Script.Base
open import Bitcoin.Script.DecidableEquality

record TxInput : Set where
  field
    txId    : HashId  -- referenced previous transaction
    index   : ℕ      -- index in the referenced transaction's outputs
    relLock : Time    -- relative timelock
open TxInput public

import Data.Set' as SET

-- Sets of transaction inputs
_≟ᵢ_ : Decidable {A = TxInput} _≡_
x ≟ᵢ y with txId x ≟ txId y | index x ≟ index y | relLock x ≟ relLock y
... | no ¬p    | _        | _        = no λ{refl → ¬p refl}
... | _        | no ¬p    | _        = no λ{refl → ¬p refl}
... | _        | _        | no ¬p    = no λ{refl → ¬p refl}
... | yes refl | yes refl | yes refl = yes refl

module SETᵢ = SET {A = TxInput} _≟ᵢ_

Set⟨TxInput⟩ : Set
Set⟨TxInput⟩ = Set' where open SETᵢ

record TxOutput (n : ℕ) : Set where
  field
    value     : Value
    validator : BitcoinScript n
open TxOutput public
∃TxOutput = ∃[ n ] TxOutput n

Witness : ℕ → Set
Witness n = Vec ℤ n

∃Witness = ∃[ n ] Witness n

record Tx (i o : ℕ) : Set where
  field
    inputs  : Vec TxInput i    -- inputs
    wit     : Vec ∃Witness i   -- segragated witnesses
    outputs : Vec ∃TxOutput o  -- outputs
    absLock : Time             -- absolute timelock
open Tx public
∃Tx = ∃[ i ] ∃[ o ] Tx i o

variable i o : ℕ

_‼ʷ_ : Tx i o → Fin i → ∃Witness
tx ‼ʷ i = lookup (wit tx) i

_‼ⁱ_ : Tx i o → Fin i → TxInput
tx ‼ⁱ i = lookup (inputs tx) i

Coinbase : Tx 0 o → Set
Coinbase tx = absLock tx ≡ 0

------------------------------------------------------------------------
-- Set modules/types.

-- Sets of outputs
_≟ₒ_ : Decidable {A = TxOutput n} _≡_
_≟ₒ_ {n} x y with value x ≟ value y | (n , validator x) SET∃ₛ.≣ (n , validator y)
... | no ¬p    | _        = no λ{refl → ¬p refl}
... | _        | no ¬p′   = no λ{refl → ¬p′ refl}
... | yes refl | yes refl = yes refl

_≟∃₀_ : Decidable {A = ∃TxOutput} _≡_
(n , x) ≟∃₀ (n′ , y)
  with n ≟ n′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl
  with x ≟ₒ y
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl

module SETₒ = SET {A = ∃TxOutput} _≟∃₀_

Set⟨∃TxOutput⟩ : Set
Set⟨∃TxOutput⟩ = Set' where open SETₒ

-- Sets of transactions
{-
postulate
  _≟≟_ : Decidable {A = Set⟨TxInput⟩} _≡_

-- | ≡-dec _≟ℤ_ (witness x) (witness y)

_≟ₜₓ_ : Decidable {A = Tx} _≡_
x ≟ₜₓ y with inputs x ≟≟ inputs y | outputs x SETₒ.≟ₗ outputs y | absLock x ≟ absLock y
... | no ¬p    | _        | _        = no λ{refl → ¬p refl}
... | _        | no ¬p′   | _        = no λ{refl → ¬p′ refl}
... | _        | _        | no ¬p′   = no λ{refl → ¬p′ refl}
... | yes refl | yes refl | yes refl = yes refl

module SETₜₓ = SET {A = Tx} _≟ₜₓ_

Set⟨Tx⟩ : Set
Set⟨Tx⟩ = Set' where open SETₜₓ
-}

-- Public-key cryptography.

postulate
  -- hashing
  HASH : ℤ → ℤ

  -- signing/verifying
  SIG : KeyPair → A → ℤ
  -- VER : KeyPair → ℤ → Bool
  VER : KeyPair → ℤ → A → Bool

-- signature modifiers
data Modifier : Set where
  aa an as sa sn ss : Modifier

keepSingleWitness : Tx i o → Fin i → Tx i o
keepSingleWitness {i = suc _} tx i′ = record tx { wit = (V.replicate (0 , V.[])) [ 0F ]≔ (1 , V.[ + (toℕ i′) ]) }

removeOutputs : Tx i o → Tx i 0
removeOutputs tx = record { inputs = inputs tx; wit = wit tx; outputs = V.[]; absLock = absLock tx }

trimOutputs : ∀ {o′} {pr : o′ ≤ o} → Tx i o → Tx i o′
trimOutputs {pr = pr} tx = record { inputs = inputs tx; wit = wit tx; outputs = go {pr = pr} (outputs tx); absLock = absLock tx }
  where
    falseOut : ∃TxOutput
    falseOut = 0 , record { value = 0; validator = ƛ `false }

    go : ∀ {o′} {pr : o′ ≤ o} → Vec ∃TxOutput o → Vec ∃TxOutput o′
    go {pr = z≤n}     _            = V.[]
    go {pr = s≤s z≤n} (o V.∷ V[]) = V.[ o ]
    go {pr = s≤s pr}  (_ V.∷ os)  = falseOut V.∷ go {pr = pr} os

keepSingleInput : Tx i o → Fin i → Tx 1 o
keepSingleInput tx i = record { inputs = V.[ tx ‼ⁱ i ] ; wit = V.[ tx ‼ʷ i ] ; outputs = outputs tx; absLock = absLock tx }

apply-aa : Tx i o → Fin i → Tx i o
apply-aa tx i = keepSingleWitness tx i

apply-an : Tx i o → Fin i → Tx i 0
apply-an tx i = apply-aa (removeOutputs tx) i

apply-as : ∀ {o′} {pr : o′ ≤ o} → Tx i o → Fin i → Tx i o′
apply-as {pr = pr} tx i = apply-aa (trimOutputs {pr = pr} tx) i

apply-sa : Tx i o → Fin i → Tx 1 o
apply-sa tx i = apply-aa (keepSingleInput tx i) 0F

modify : Modifier → Tx i o → Fin i → ∃Tx
modify aa tx i = _ , _ , apply-aa tx i
modify an tx i = _ , _ , apply-an tx i
modify as tx i = {!!} -- _ , _ , apply-as tx i
modify sa tx i = _ , _ , apply-sa tx i
modify sn tx i = _ , _ , apply-sa (apply-an tx i) i
modify ss tx i = {!!} -- _ , _ , apply-sa (apply-as tx i) i

record Signature : Set where
  field
    signature : ℤ
    modifier  : Modifier
open Signature public

sig : KeyPair → Modifier → Tx i o → Fin i → Signature
sig k μ tx i = record { signature = SIG k (modify μ tx i , μ); modifier = μ }

ver : KeyPair → Signature → Tx i o → Fin i → Bool
ver k σ tx i with σ
... | record {signature = w; modifier = μ} = VER k w (modify μ tx i , μ)

-- m-of-n multi-signature scheme
ver⋆ : List KeyPair → List ℤ → Tx i o → Fin i → Bool
ver⋆ _         []        _ _ = true
ver⋆ []        _         _ _ = false
ver⋆ (k ∷ ks) (σ ∷ σs) T i = if VER k σ T then ver⋆ ks σs T i else ver⋆ (k ∷ ks) σs T i

-- Script (denotational) semantics.
record Environment (i o n : ℕ) : Set where
  field
    tx      : Tx i o
    index   : Fin i
    context : Vec ℤ n
open Environment public

open import Level using (0ℓ)
open import Category.Functor       using (RawFunctor)
open import Category.Applicative   using (RawApplicative)
open import Data.Maybe.Categorical using (functor; applicative)
open RawFunctor {0ℓ} functor
open RawApplicative {0ℓ} applicative
_<*>_ = _⊛_

infix 8 ⟦_⟧′_
⟦_⟧′_ : Script n A → Environment i o n → Maybe A
⟦ var x                ⟧′ ρ = ⦇ (lookup (context ρ) x) ⦈
⟦ ` x                  ⟧′ ρ = ⦇ x ⦈
⟦ e `+ e′              ⟧′ ρ = ⦇ ⟦ e ⟧′ ρ + ⟦ e′ ⟧′ ρ ⦈
⟦ e `- e′              ⟧′ ρ = ⦇ ⟦ e ⟧′ ρ - ⟦ e′ ⟧′ ρ ⦈
⟦ e `= e′              ⟧′ ρ
  -- ⦇ ⌊ ⟦ e ⟧′ ρ ≟ℤ ⟦ e′ ⟧′ ρ ⌋ ⦈
  with ⟦ e ⟧′ ρ | ⟦ e′ ⟧′ ρ
... | just me | just me′ = just ⌊ me ≟ℤ me′ ⌋
... | nothing | _        = nothing
... | _       | nothing  = nothing
⟦ e `< e′              ⟧′ ρ
  -- ⦇ ⌊ ⟦ e ⟧′ ρ <? ⟦ e′ ⟧′ ρ ⌋ ⦈
  with ⟦ e ⟧′ ρ | ⟦ e′ ⟧′ ρ
... | just me | just me′ = just ⌊ me <? me′ ⌋
... | nothing | _        = nothing
... | _       | nothing  = nothing
⟦ `if b then e else e′ ⟧′ ρ = ⦇ if ⟦ b ⟧′ ρ then ⟦ e ⟧′ ρ else ⟦ e′ ⟧′ ρ ⦈
-- ⟦ ∣ e ∣                 ⟧′ ρ = {!!}
⟦ hash e               ⟧′ ρ = ⦇ HASH (⟦ e ⟧′ ρ) ⦈
⟦ versig k σ           ⟧′ ρ = just (ver⋆ k (map (lookup (context ρ)) σ) (tx ρ) (index ρ))
⟦ absAfter t ⦂ e       ⟧′ ρ with absLock (tx ρ) ≥? t
... | yes _ = ⟦ e ⟧′ ρ
... | no  _ = nothing

⟦ relAfter t ⦂ e       ⟧′ ρ with relLock (tx ρ ‼ⁱ index ρ) ≥? t
... | yes _ = ⟦ e ⟧′ ρ
... | no  _ = nothing

⟦_⟧_ : BitcoinScript n → Environment i o n → Bool
⟦ ƛ x ⟧ ρ = fromMaybe false (⟦ x ⟧′ ρ)

-- Script verification
_,_⊨_ : (tx : Tx i o) → (i : Fin i) → BitcoinScript n → {pr : proj₁ (tx ‼ʷ i) ≡ n} → Set
(tx , i ⊨ e) {pr = refl} = T (⟦ e ⟧ record { tx = tx ; index = i ; context = proj₂ (tx ‼ʷ i) })

-- runValidation : Tx i o → TxInput n → TxOutput n → Bool
-- runValidation tx i o = ⟦ validator o ⟧ record { tx = tx ; index = {!!} ; context = wit i }
