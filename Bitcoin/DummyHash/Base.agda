---------------------------------------------------------------------------------
-- Concrete "dummy" hashing functions, for use in examples.
-- NB: in contrast to postulated cryptographic function, these will compute
---------------------------------------------------------------------------------
module Bitcoin.DummyHash.Base where

open import Function using (_∘_)

open import Data.Product     using (_×_; _,_)
open import Data.Nat         using (ℕ)
open import Data.Integer     using (ℤ; +_; ∣_∣)
open import Data.Char        using (toℕ)
open import Data.String as S using (String)
open import Data.List        using (List; sum; map; _∷_; [])
open import Data.Vec as V    using (Vec)

open import Bitcoin.BasicTypes

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
