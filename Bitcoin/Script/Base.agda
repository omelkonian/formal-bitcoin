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
open import Bitcoin.Crypto

data ScriptContext : Set where
  Ctx : ℕ → ScriptContext

ctxToℕ : ScriptContext → ℕ
ctxToℕ (Ctx n) = n

data ScriptType : Set where
  `Bool `ℤ : ScriptType

variable
  ctx ctx′ : ScriptContext
  ty ty′ : ScriptType

data Script : ScriptContext  -- size of the environment/context
            → ScriptType     -- result type
            → Set where

  -- Variables
  var  : Fin n → Script (Ctx n) `ℤ

  -- Arithmetic/boolean operations
  `    : ℤ → Script ctx `ℤ
  _`+_ : Script ctx `ℤ → Script ctx `ℤ → Script ctx `ℤ
  _`-_ : Script ctx `ℤ → Script ctx `ℤ → Script ctx `ℤ
  _`=_ : Script ctx `ℤ → Script ctx `ℤ → Script ctx `Bool
  _`<_ : Script ctx `ℤ → Script ctx `ℤ → Script ctx `Bool

  -- Conditional statement
  `if_then_else_ : Script ctx `Bool → Script ctx ty → Script ctx ty → Script ctx ty

  -- Size
  ∣_∣ : Script ctx `ℤ → Script ctx `ℤ

  -- Hashing
  hash : Script ctx `ℤ → Script ctx `ℤ

  -- Signature verification
  versig : List KeyPair → List (Fin n) → Script (Ctx n) `Bool

  -- Temporal constraints
  absAfter_⇒_ : Time → Script ctx ty → Script ctx ty
  relAfter_⇒_ : Time → Script ctx ty → Script ctx ty

∃Script = ∃[ ctx ] ∃[ ty ] Script ctx ty

`false : Script ctx `Bool
`false = ` (+ 1) `= ` (+ 0)

`true : Script ctx `Bool
`true = ` (+ 1) `= ` (+ 1)

_`∧_ : Script ctx `Bool → Script ctx `Bool → Script ctx `Bool
e `∧ e′ = `if e then e′ else `false

_`∨_ : Script ctx `Bool → Script ctx `Bool → Script ctx `Bool
e `∨ e′ = `if e then `true else e′

`not : Script ctx `Bool → Script ctx `Bool
`not e = `if e then `false else `true

data BitcoinScript (ctx : ScriptContext) : Set where
  ƛ_ : Script ctx `Bool → BitcoinScript ctx

∃BitcoinScript = ∃[ ctx ] BitcoinScript ctx

-- operators' precedence
infix  5 _`+_
infix  5 _`-_
infix  4 _`=_
infix  4 _`<_
infixr 3 _`∨_
infixr 3 _`∧_
infix  2 `if_then_else_
infix  2 absAfter_⇒_
infix  2 relAfter_⇒_
infix  1 ƛ_

_ : BitcoinScript (Ctx 2)
_ = ƛ versig [] [ FZ ] `∧ (hash (var (FS FZ)) `= hash (var FZ))
