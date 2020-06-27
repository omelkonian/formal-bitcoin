------------------------------------------------------------------------
-- Public-key cryptography.
------------------------------------------------------------------------
module Bitcoin.Crypto where

open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq

open import Bitcoin.BasicTypes

record KeyPair : Set where
  field
    pub : ℤ
    sec : ℤ
open KeyPair public

unquoteDecl DecEqᵏᵖ = DERIVE DecEq [ quote KeyPair , DecEqᵏᵖ ]

private
  variable
    A B : Set

postulate
  -- hashing function
  HASH : A → ℤ

  -- signing/verifying
  SIG : KeyPair → A → ℤ
  VER : KeyPair → ℤ → A → Bool
  VERSIG≡ : ∀ {k : KeyPair} {x : A} → T (VER k (SIG k x) x)

-- Concrete "dummy" hashing functions, for use in examples (so that they compute)
open import Function using (_∘_)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; sum; map; _∷_; [])
open import Data.Vec as V using (Vec)
open import Data.Integer using (+_; ∣_∣)
open import Data.Nat using (ℕ)
open import Data.String as S using (String)
open import Data.Char using (toℕ)

HashFunction : Set → Set
HashFunction A = A → ℤ

merge♯ : List ℤ → ℤ
merge♯ = +_ ∘ sum ∘ map ∣_∣

nat♯ : HashFunction ℕ
nat♯ = +_

list♯ : HashFunction A → HashFunction (List A)
list♯ h = merge♯ ∘ map h

vec♯ : HashFunction A → HashFunction (Vec A n)
vec♯ h = list♯ h ∘ V.toList

pair♯ : HashFunction A → HashFunction B → HashFunction (A × B)
pair♯ h₁ h₂ (a , b) = merge♯ (h₁ a ∷ h₂ b ∷ [])

str♯ : HashFunction String
str♯ = list♯ (+_ ∘ toℕ) ∘ S.toList
