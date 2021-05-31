------------------------------------------------------------------------
-- Public-key cryptography.
------------------------------------------------------------------------
module Bitcoin.Crypto where

open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.ToN

open import Bitcoin.BasicTypes

record KeyPair : Set where
  field
    pub : ℤ
    sec : ℤ
open KeyPair public
unquoteDecl DecEqᵏᵖ = DERIVE DecEq [ quote KeyPair , DecEqᵏᵖ ]

private variable A B : Set

HashFunction : Set ℓ → Set ℓ
HashFunction A = A → ℤ

postulate
  -- universal hashing function
  HASH : HashFunction A

  -- signing/verifying
  SIG : KeyPair → A → ℤ
  VER : KeyPair → ℤ → A → Bool
  VERSIG≡ : ∀ {k : KeyPair} {x : A} → T (VER k (SIG k x) x)

record Hashable {ℓ} (A : Set ℓ) : Set ℓ where
  field
    _♯ : HashFunction A
open Hashable ⦃ ... ⦄ public

-- Concrete "dummy" hashing functions, for use in examples (so that they compute)

merge♯ : List ℤ → ℤ
merge♯ = +_ ∘ sum ∘ map Integer.∣_∣

instance
  Hashable-ℤ : Hashable ℤ
  Hashable-ℤ ._♯ = id

  Hashable-Bool : Hashable Bool
  Hashable-Bool ._♯ = if_then + 1 else + 0

  Hashable-ℕ : Hashable ℕ
  Hashable-ℕ ._♯ = +_

  Hashable-Char : Hashable Char
  Hashable-Char ._♯ c = toℕ c ♯

  Hashable-Fin : Hashable (Fin n)
  Hashable-Fin ._♯ = _♯ ∘ toℕ

  Hashable-List : ⦃ _ : Hashable A ⦄ → Hashable (List A)
  Hashable-List ._♯ xs = merge♯ $ map _♯ xs

  Hashable-Vec : ⦃ _ : Hashable A ⦄ → Hashable (Vec A n)
  Hashable-Vec ._♯ = _♯ ∘ V.toList

  Hashable-String : Hashable String
  Hashable-String ._♯ = _♯ ∘ Str.toList

  -- Deriving the hash of a dependent pair from hashing its parts.
  Hashable-Σ : ∀ {A : Set} {B : A → Set} ⦃ _ : Hashable A ⦄ ⦃ _ : ∀ {x} → Hashable (B x) ⦄ → Hashable (Σ A B)
  Hashable-Σ ._♯ (x , y) = merge♯ (x ♯ ∷ y ♯ ∷ [])

  -- Deriving the hash of a union type.
  Hashable-⊎ : ⦃ _ : Hashable A ⦄ ⦃ _ : Hashable B ⦄ → Hashable (A ⊎ B)
  Hashable-⊎ ._♯ (inj₁ x) = (true  , x) ♯
  Hashable-⊎ ._♯ (inj₂ y) = (false , y) ♯

  Hashable-KeyPair : Hashable KeyPair
  Hashable-KeyPair ._♯ k = (pub k , sec k) ♯
