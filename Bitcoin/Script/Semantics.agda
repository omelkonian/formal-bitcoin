------------------------------------------------------------------------
-- Denotational semantics for Bitcoin scripts.
------------------------------------------------------------------------
module Bitcoin.Script.Semantics where

open import Data.Integer    using (_+_; _-_)
open import Data.Nat.Binary using (fromℕ) renaming (size to digits)
open import Data.Nat.DivMod using (_/_)

open import Prelude.Init hiding (_+_); open SetAsType
open V hiding ([_])
open import Prelude.DecEq
open import Prelude.Ord
open import Prelude.Functor
open import Prelude.Applicative

open import Bitcoin.BasicTypes
open import Bitcoin.Crypto
open import Bitcoin.Script.Base
open import Bitcoin.Tx.Base
open import Bitcoin.Tx.Crypto

record Environment (i o : ℕ) (ctx : ScriptContext) : Type where
  field tx  : Tx i o
        ix  : Fin i
        val : Vec ℤ ctx
open Environment public

⟦_⟧ₜ : ScriptType → Type
⟦ `Bool ⟧ₜ = Bool
⟦ `ℤ    ⟧ₜ = ℤ

infix 8 ⟦_⟧′_
⟦_⟧′_ : Script ctx ty → Environment i o ctx → Maybe ⟦ ty ⟧ₜ
⟦ e ⟧′ ρ = case e of λ where
  (var x)                → ⦇ (lookup (ρ .val) x) ⦈
  (` x)                  → ⦇ x ⦈
  (e `+ e′)              → ⦇ ⟦ e ⟧′ ρ + ⟦ e′ ⟧′ ρ ⦈
  (e `- e′)              → ⦇ ⟦ e ⟧′ ρ - ⟦ e′ ⟧′ ρ ⦈
  (e `= e′)              → ⦇ ⟦ e ⟧′ ρ == ⟦ e′ ⟧′ ρ ⦈
  (e `< e′)              → ⦇ ⟦ e ⟧′ ρ <ᵇ ⟦ e′ ⟧′ ρ ⦈
  (`if b then e else e′) → ⦇ if ⟦ b ⟧′ ρ then ⟦ e ⟧′ ρ else ⟦ e′ ⟧′ ρ ⦈
  (∣ e ∣)                → ⦇ size (⟦ e ⟧′ ρ) ⦈
  (hash e)               → ⦇ (⟦ e ⟧′ ρ) ♯ ⦈
  (versig k σ)           → just $ ver⋆ k (lookup (ρ .val) <$> σ) (ρ .tx) (ρ .ix)
  (absAfter t ⇒ e)       → if ρ .tx .absLock ≥ᵇ t then ⟦ e ⟧′ ρ else nothing
  (relAfter t ⇒ e)       → if ρ .tx ‼ʳ ρ .ix ≥ᵇ t then ⟦ e ⟧′ ρ else nothing
 where size : ℤ → ℤ
       size x = + (suc (digits (fromℕ Integer.∣ x ∣)) / 7)
       -- T0D0 ceiling (must involve floats...)

⟦_⟧_ : BitcoinScript ctx → Environment i o ctx → Bool
⟦ ƛ x ⟧ ρ = M.fromMaybe false (⟦ x ⟧′ ρ)

-- Script verification
infix 0 _,_⊨_ _,_⊭_

_,_⊨_ : (tx : Tx i o) (i : Fin i) → BitcoinScript ctx → ⦃ ctx ≡ (tx ‼ʷ i) .proj₁ ⦄ → Type
(tx , i ⊨ e) ⦃ refl ⦄ = T (⟦ e ⟧ record { tx = tx ; ix = i ; val = (tx ‼ʷ i) .proj₂ })

_,_⊭_ : (tx : Tx i o) (i : Fin i) → BitcoinScript ctx → ⦃ ctx ≡ (tx ‼ʷ i) .proj₁ ⦄ → Type
tx , i ⊭ e = ¬ (tx , i ⊨ e)

open import Prelude.InferenceRules
⊨-elim : (tx : Tx i o) (i : Fin i) (e : BitcoinScript ctx)
         ⦃ eq eq′ : ctx ≡ (tx ‼ʷ i) .proj₁ ⦄ →
  ∙ (tx , i ⊨ e) ⦃ eq ⦄
  ∙ (tx , i ⊭ e) ⦃ eq′ ⦄
    ────────────────────
    ⊥
⊨-elim tx i e ⦃ refl ⦄ ⦃ refl ⦄ p ¬p = ¬p p

module Example2
  {σ s : HashId} {t k txi}
  {i} {is : Vec TxInput i} {ws} {rs}
  {o} {os : Vec ∃TxOutput o}
  (let h = s ♯
       T = record { inputs = txi ∷ is
                  ; wit = (2 , σ ∷ s ∷ []) ∷ ws
                  ; relLock = rs
                  ; outputs = os
                  ; absLock = t })
  (σ≡ : σ ≡ SIG k (μ T 0F))
  where
  open import Prelude.General
  open ≡-Reasoning

  _ : T , 0F ⊨ ƛ versig [ k ] [ 0F ] `∧ (hash (var 1F) `= ` h)
  _ rewrite begin ver⋆ [ k ] [ σ ] T 0F ≡⟨ if-eta _ ⟩
                  VER k σ _             ≡⟨ cong (λ ◆ → VER _ ◆ _) σ≡ ⟩
                  VER k (SIG k _) _     ≡⟨ T⇒true VERSIG≡ ⟩
                  true                  ∎
          | ≟-refl h
          = tt
