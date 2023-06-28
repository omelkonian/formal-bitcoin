------------------------------------------------------------------------
-- Examples 5,6,7 from the paper.
------------------------------------------------------------------------
{-# OPTIONS --rewriting #-}
module Bitcoin.Examples where

open import Agda.Builtin.Equality.Rewrite

open import Prelude.Init; open SetAsType
open Nat using (≤-refl; m≤m+n)
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Sets
open import Prelude.Setoid
open import Prelude.Decidable
open import Prelude.FromList

open import Bitcoin.Crypto
open import Bitcoin.BasicTypes
open import Bitcoin.Script
open import Bitcoin.Tx
open import Bitcoin.Consistency

postulate
  k₁ k₂ k₃ : KeyPair
  t₂ t₃ : Time

T₁ : Tx 0 3
T₁ = record
  { inputs  = []
  ; wit     = []
  ; relLock = []
  ; outputs = (1 , 3 locked-by ƛ versig [ k₁ ] [ 0F ])
            ∷ (1 , 5 locked-by ƛ versig [ k₂ ] [ 0F ])
            ∷ (1 , 7 locked-by ƛ versig [ k₃ ] [ 0F ])
            ∷ []
  ; absLock = 0 }

T₂ : Tx 2 1
T₂ = sig⋆ ([ k₂ ] ∷ [ k₃ ] ∷ []) record
  { inputs  = (T₁ ♯) at 1
            ∷ (T₁ ♯) at 2
            ∷ []
  ; wit     = wit⊥
  ; relLock = 0
            ∷ 0
            ∷ []
  ; outputs = V.[ 1 , 10 locked-by ƛ versig [ k₂ ] [ 0F ] ]
  ; absLock = t₂ }

T₃ : Tx 1 1
T₃ = sig⋆ V.[ [ k₂ ] ] record
  { inputs  = V.[ (T₁ ♯) at 1 ]
  ; wit     = wit⊥
  ; relLock = V.[ 0 ]
  ; outputs = V.[ 1 , 5 locked-by ƛ versig [ k₂ ] [ 0F ] ]
  ; absLock = t₃ }

B : Blockchain
B = (-, -, T₂) at t₂ ∷ (-, -, T₁) at 0 ∷ []

postulate
  eq1 : (T₁ ♯) ≡ + 1
  eq2 : (T₂ ♯) ≡ + 2
  eq3 : (T₃ ♯) ≡ + 3
{-# REWRITE eq1 #-}
{-# REWRITE eq2 #-}
{-# REWRITE eq3 #-}

_≈?ˢ_ : ∀ (x y : Set⟨ TxInput ⟩) → Dec (x ≈ y)
x ≈?ˢ y = (x ⊆?ˢ y) ×-dec (y ⊆?ˢ x)

b = List TxInput ∋ (T₁ ♯) at 0 ∷ (T₂ ♯) at 0 ∷ []

_ : UTXO B ≈ fromList b
_ = toWitness {Q = UTXO B ≈?ˢ fromList b} tt

B₀ : Blockchain
B₀ = [ (-, -, T₁) at 0 ]

b₀ = List TxInput ∋ (T₁ ♯) at 0 ∷ (T₁ ♯) at 1 ∷ (T₁ ♯) at 2 ∷ []

_ : UTXO B₀ ≈ fromList b₀
_ = toWitness {Q = UTXO B₀ ≈?ˢ fromList b₀} tt

_ : B₀ ▷ T₂ , t₂
_ = record
  { inputsUnique = auto
  ; singleMatch = λ where
      0F → -, refl
      1F → -, refl
  ; noOutOfBounds = λ where
      0F → m≤m+n _ 1
      1F → ≤-refl
  ; inputs∈UTXO = λ where
      0F → auto
      1F → auto
  ; inputsRedeemable = λ where
      0F → record
        { input~output = refl
        ; scriptValidates = ver⋆sig≡ T₂ 0F
        ; value≡ = refl
        ; satisfiesAbsLock = ≤-refl
        ; satisfiesRelLock = z≤n , z≤n
        }
      1F → record
        { input~output = refl
        ; scriptValidates = ver⋆sig≡ T₂ 1F
        ; value≡ = refl
        ; satisfiesAbsLock = ≤-refl
        ; satisfiesRelLock = z≤n , z≤n
        }
  ; valuesPreserved = m≤m+n _ 2
  ; laterTime = z≤n
  }

_ : ¬ (B ▷ T₃ , t₃)
_ = λ where record {inputs∈UTXO = p} → contradict (p 0F)
