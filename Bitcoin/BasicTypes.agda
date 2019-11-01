------------------------------------------------------------------------
-- Basic types.
------------------------------------------------------------------------
module Bitcoin.BasicTypes where

open import Data.Nat     using (ℕ)
open import Data.Integer using (ℤ)

Value : Set
Value = ℕ

$ : ℕ → ℕ
$ v = v

Time : Set
Time = ℕ

HashId : Set
HashId = ℤ

variable
  A B C : Set
  n n′ : ℕ
  t t′ : Time
