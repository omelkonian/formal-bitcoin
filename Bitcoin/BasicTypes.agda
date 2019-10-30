------------------------------------------------------------------------
-- Basic types.
------------------------------------------------------------------------
module Bitcoin.BasicTypes where

open import Data.Nat  using (ℕ)

Value : Set
Value = ℕ

$ : ℕ → ℕ
$ v = v

HashId : Set
HashId = ℕ

Time : Set
Time = ℕ

