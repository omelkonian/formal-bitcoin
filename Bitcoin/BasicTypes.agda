------------------------------------------------------------------------
-- Basic types.
------------------------------------------------------------------------
module Bitcoin.BasicTypes where

open import Prelude.Init

Value : Set
Value = ℕ

Time : Set
Time = ℕ

HashId : Set
HashId = ℤ

variable
  n n′ : ℕ
  t t′ : Time
