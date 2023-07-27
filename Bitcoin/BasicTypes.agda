------------------------------------------------------------------------
-- Basic types.
------------------------------------------------------------------------
module Bitcoin.BasicTypes where

open import Prelude.Init; open SetAsType
open Nat using (_<ᵇ_)

Value  = ℕ -- amount in Satoshis
Time   = ℕ -- Unit time: number of seconds since 1/1/1970
HashId = ℤ -- hashes as integers
-- HashId = Bitstring

variable
  n n′ : ℕ
  t t′ : Time

-- ** Calendar dates in Unix time.
_seconds _minutes _hours _days _months _years : Op₁ Time
_seconds = id
_minutes = _* 60
_hours   = _minutes ∘ (_* 60)
_days    = _hours   ∘ (_* 24)
_months  = _days    ∘ (_* 30)
_years   = _months  ∘ (_* 12)

record Date : Type where
  constructor _/_/_
  field day month year : ℕ

infix 10 date∶_
date∶_ : Date → Time
date∶ d / m / y = if y <ᵇ 1970 then 0 else (y ∸ 1970) years + m months + d days
