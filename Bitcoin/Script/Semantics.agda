------------------------------------------------------------------------
-- Denotational semantics for Bitcoin scripts.
------------------------------------------------------------------------
module Bitcoin.Script.Semantics where

open import Data.Empty          using (⊥-elim)
open import Data.Unit           using (tt)
open import Data.Product        using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.Bool           using (Bool; true; false; T; if_then_else_)
open import Data.Maybe          using (Maybe; just; nothing; fromMaybe)
open import Data.Fin as F       using (Fin)
open import Data.Fin.Patterns   using (0F; 1F)
open import Data.Nat            using (ℕ; suc; _≟_; _∸_; _≤_; s≤s; z≤n; _≥_; _≥?_)
  renaming (_+_ to _+ℕ_)
open import Data.Integer        using (ℤ; +_; _+_; _-_; _<_; _<?_)
  renaming (_≟_ to _≟ℤ_; ∣_∣ to abs)
open import Data.Nat.Binary     using (fromℕ)
  renaming (size to digits)
open import Data.Nat.DivMod     using (_/_)
open import Data.List           using (List; []; [_]; _∷_; map)
open import Data.Vec as V       using (Vec; lookup; _[_]≔_)
open import Data.Vec.Properties using (≡-dec)

open import Relation.Nullary                      using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable            using (⌊_⌋)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Bitcoin.BasicTypes
open import Bitcoin.Crypto
open import Bitcoin.Script.Base
open import Bitcoin.Tx.Base
open import Bitcoin.Tx.Crypto

record Environment (i o : ℕ) (ctx : ScriptContext) : Set where
  field
    tx      : Tx i o
    index   : Fin i
    context : Vec ℤ (ctxToℕ ctx)
open Environment public

open import Level using (0ℓ)
open import Category.Functor       using (RawFunctor)
open import Category.Applicative   using (RawApplicative)
open import Data.Maybe.Categorical using (functor; applicative)
open RawFunctor {0ℓ} functor
open RawApplicative {0ℓ} applicative
_<*>_ = _⊛_

⟦_⟧ₜ : ScriptType → Set
⟦_⟧ₜ `Bool = Bool
⟦_⟧ₜ `ℤ    = ℤ

infix 8 ⟦_⟧′_
⟦_⟧′_ : Script ctx ty → Environment i o ctx → Maybe ⟦ ty ⟧ₜ
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
⟦ ∣ e ∣                ⟧′ ρ = ⦇ size (⟦ e ⟧′ ρ) ⦈
  where
    size : ℤ → ℤ
    size x = + (suc (digits (fromℕ (abs x))) / 7) -- T0D0 ceiling (must involve floats...)
⟦ hash e               ⟧′ ρ = ⦇ HASH (⟦ e ⟧′ ρ) ⦈
⟦ versig k σ           ⟧′ ρ = just (ver⋆ k (map (lookup (context ρ)) σ) (tx ρ) (index ρ))
⟦ absAfter t ⇒ e       ⟧′ ρ with absLock (tx ρ) ≥? t
... | yes _ = ⟦ e ⟧′ ρ
... | no  _ = nothing

⟦ relAfter t ⇒ e       ⟧′ ρ with tx ρ ‼ʳ index ρ ≥? t
... | yes _ = ⟦ e ⟧′ ρ
... | no  _ = nothing

⟦_⟧_ : BitcoinScript ctx → Environment i o ctx → Bool
⟦ ƛ x ⟧ ρ = fromMaybe false (⟦ x ⟧′ ρ)

-- Script verification
infix 5 _,_⊨_
_,_⊨_ : (tx : Tx i o) → (i : Fin i) → BitcoinScript ctx → {pr : ctx ≡ Ctx (proj₁ (tx ‼ʷ i))} → Set
_,_⊨_ {ctx = Ctx _} tx i e {pr = refl} = T (⟦ e ⟧ record { tx = tx ; index = i ; context = proj₂ (tx ‼ʷ i) })

module Example2 where

  ex2 : ∀ {σ s h : ℤ} {k : KeyPair}
          {txi : TxInput} {i} {is : Vec TxInput i} {ws : Vec ∃Witness i} {rs : Vec Time (suc i)}
          {o} {os : Vec ∃TxOutput o} {t : Time}
          {h≡ : HASH s ≡ h}
      → let t = record { inputs = txi V.∷ is
                        ; wit = (2 , σ V.∷ s V.∷ V.[]) V.∷ ws
                        ; relLock = rs
                        ; outputs = os
                        ; absLock = t } in
         {σ≡ : ver⋆ [ k ] [ σ ] t 0F ≡ true}
      → (t , 0F ⊨ (ƛ (versig [ k ] [ 0F ] `∧ (hash (var {n = 2} 1F) `= ` h)))) {pr = refl}
  ex2 {h≡ = h≡} {σ≡ = σ≡} rewrite h≡ | σ≡ = taut
    where
      taut : ∀ {w} → T ⌊ w ≟ℤ w ⌋
      taut {w} with w ≟ℤ w
      ... | yes p = tt
      ... | no ¬p = ⊥-elim (¬p refl)
