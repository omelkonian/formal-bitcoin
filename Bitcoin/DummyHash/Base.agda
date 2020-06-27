---------------------------------------------------------------------------------
-- Concrete "dummy" hashing functions, for use in examples.
-- NB: in contrast to postulated cryptographic function, these will compute
---------------------------------------------------------------------------------
module Bitcoin.DummyHash.Base where

open import Prelude.Init
open import Prelude.ToN

open import Bitcoin.BasicTypes

private
  variable
    A B : Set

HashFunction : Set → Set
HashFunction A = A → ℤ

merge♯ : List ℤ → ℤ
merge♯ = +_ ∘ sum ∘ map Integer.∣_∣

nat♯ : HashFunction ℕ
nat♯ = +_

list♯ : HashFunction A → HashFunction (List A)
list♯ h = merge♯ ∘ map h

vec♯ : HashFunction A → HashFunction (Vec A n)
vec♯ h = list♯ h ∘ V.toList

pair♯ : HashFunction A → HashFunction B → HashFunction (A × B)
pair♯ h₁ h₂ (a , b) = merge♯ (h₁ a ∷ h₂ b ∷ [])

str♯ : HashFunction String
str♯ = list♯ (+_ ∘ toℕ) ∘ Str.toList
