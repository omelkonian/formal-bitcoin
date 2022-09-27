------------------------------------------------------------------------
-- Public-key cryptography.
------------------------------------------------------------------------
module Bitcoin.Crypto where

open import Prelude.Init
open import Prelude.DecEq

open import Bitcoin.BasicTypes

record KeyPair : Set where
  field pub : HashId
        sec : HashId
open KeyPair public
unquoteDecl DecEqᵏᵖ = DERIVE DecEq [ quote KeyPair , DecEqᵏᵖ ]

HashFunction : Set ℓ → Set ℓ
HashFunction A = A → HashId

private variable A : Set

postulate
  -- universal hashing function
  _♯ : HashFunction A

  -- signing/verifying
  SIG : KeyPair → A → HashId
  VER : KeyPair → HashId → A → Bool
  VERSIG≡ : ∀ {k : KeyPair} {x : A} → T (VER k (SIG k x) x)
