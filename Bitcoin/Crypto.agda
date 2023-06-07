------------------------------------------------------------------------
-- Public-key cryptography.
------------------------------------------------------------------------
module Bitcoin.Crypto where

open import Prelude.Init; open SetAsType
open import Prelude.DecEq

open import Bitcoin.BasicTypes

record KeyPair : Type where
  field pub : HashId
        sec : HashId
open KeyPair public
unquoteDecl DecEqᵏᵖ = DERIVE DecEq [ quote KeyPair , DecEqᵏᵖ ]

HashFunction : Type ℓ → Type ℓ
HashFunction A = A → HashId

private variable A : Type

postulate
  -- universal hashing function
  _♯ : HashFunction A

  -- signing/verifying
  SIG : KeyPair → A → HashId
  VER : KeyPair → HashId → A → Bool
  VERSIG≡ : ∀ {k : KeyPair} {x : A} → T (VER k (SIG k x) x)
