------------------------------------------------------------------------
-- Public-key cryptography.
------------------------------------------------------------------------
module Bitcoin.Crypto where

open import Data.Bool    using (Bool; T)
open import Data.Integer using (ℤ)

open import Bitcoin.BasicTypes

record KeyPair : Set where
  field
    pub : ℤ
    sec : ℤ
open KeyPair public

postulate
  -- hashing function
  HASH : A → ℤ

  -- signing/verifying
  SIG : KeyPair → A → ℤ
  VER : KeyPair → ℤ → A → Bool
  VERSIG≡ : ∀ {k : KeyPair} {x : A} → T (VER k (SIG k x) x)
