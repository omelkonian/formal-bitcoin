------------------------------------------------------------------------
-- Basic Script datatype.
------------------------------------------------------------------------
module Bitcoin.Script.Base where

open import Data.Bool    using (Bool)
open import Data.Nat     using (ℕ)
open import Data.Product using (∃-syntax)
open import Data.List    using (List; []; [_])
open import Data.Fin     using (Fin) renaming (zero to FZ; suc to FS)
open import Data.Integer using (ℤ; +_)

open import Bitcoin.BasicTypes

--------------------------------------------------------------------------------------
-- Bitcoin scripts.

variable
  n n′ : ℕ
  A : Set

record KeyPair : Set where
  field
    pub : ℤ
    sec : ℤ
open KeyPair public

data Script :  ℕ  -- size of the environment/context
            → Set -- result type
            → Set where

  -- Variables
  var  : Fin n → Script n ℤ

  -- Arithmetic/boolean operations
  `    : ℤ → Script n ℤ
  _`+_ : Script n ℤ → Script n ℤ → Script n ℤ
  _`-_ : Script n ℤ → Script n ℤ → Script n ℤ
  _`=_ : Script n ℤ → Script n ℤ → Script n Bool
  _`<_ : Script n ℤ → Script n ℤ → Script n Bool

  -- Conditional statement
  `if_then_else_ : Script n Bool → Script n A → Script n A → Script n A

  -- Size (do not support for now, needs floats, logarithms, etc...)
  -- ∣_∣ : Script n ℤ → Script n ℤ

  -- Hashing
  hash : Script n ℤ → Script n ℤ

  -- Signature verification
  versig : List KeyPair → List (Fin n) → Script n Bool

  -- Temporal constraints
  absAfter_⦂_ : Time → Script n A → Script n A
  relAfter_⦂_ : Time → Script n A → Script n A

∃Script = ∃[ n ] ∃[ A ] Script n A

`false : Script n Bool
`false = ` (+ 1) `= ` (+ 0)

`true : Script n Bool
`true = ` (+ 1) `= ` (+ 1)

_`∧_ : Script n Bool → Script n Bool → Script n Bool
e `∧ e′ = `if e then e′ else `false

_`∨_ : Script n Bool → Script n Bool → Script n Bool
e `∨ e′ = `if e then `true else e′

`not : Script n Bool → Script n Bool
`not e = `if e then `false else `true

data BitcoinScript (n : ℕ) : Set where
  ƛ_ : Script n Bool → BitcoinScript n

∃BitcoinScript = ∃[ n ] BitcoinScript n

infixr 6 _`∧_
infixr 5 _`∨_
infix  4 _`=_
infix  4 _`<_
infix  3 _`+_
infix  3 _`-_
infix  2 `if_then_else_
infix  2 absAfter_⦂_
infix  2 relAfter_⦂_
infix  1 ƛ_

_ : BitcoinScript 2
_ = ƛ versig [] [ FZ ] `∧ (hash (var (FS FZ)) `= hash (var FZ))
