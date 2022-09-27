------------------------------------------------------------------------
-- Basic types.
------------------------------------------------------------------------
module Bitcoin.BasicTypes where

open import Prelude.Init

Value  = ℕ
Time   = ℕ
HashId = ℤ
-- HashId = Bitstring

variable
  n n′ : ℕ
  t t′ : Time
