------------------------------------------------------------------------
-- Basic Script datatype.
------------------------------------------------------------------------
module Bitcoin.Script.Base where

open import Prelude.Init
open import Prelude.DecEq

open import Bitcoin.BasicTypes
open import Bitcoin.Crypto

data ScriptContext : Set where
  Ctx : ℕ → ScriptContext
unquoteDecl DecEqᶜᵗˣ = DERIVE DecEq [ quote ScriptContext , DecEqᶜᵗˣ ]

ctxToℕ : ScriptContext → ℕ
ctxToℕ (Ctx n) = n

data ScriptType : Set where
  `Bool `ℤ : ScriptType
unquoteDecl DecEqᵗʸ = DERIVE DecEq [ quote ScriptType , DecEqᵗʸ ]

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

unquoteDecl DecEqˢ = DERIVE DecEq [ quote Script , DecEqˢ ]

-- smart constructors
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

unquoteDecl DecEqᵇˢ = DERIVE DecEq [ quote BitcoinScript , DecEqᵇˢ ]

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
_ = ƛ versig [] [ 0F ] `∧ (hash (var 1F) `= hash (var 0F))

-- Combining scripts
mapFin : ∀ {n m} → n ≤ m → Script (Ctx n) ty → Script (Ctx m) ty
mapFin n≤m (var x)                 = var (F.inject≤ x n≤m)
mapFin n≤m (` x)                   = ` x
mapFin n≤m (s `+ s₁)               = mapFin n≤m s `+ mapFin n≤m s₁
mapFin n≤m (s `- s₁)               = mapFin n≤m s `- mapFin n≤m s₁
mapFin n≤m (s `= s₁)               = mapFin n≤m s `= mapFin n≤m s₁
mapFin n≤m (s `< s₁)               = mapFin n≤m s `< mapFin n≤m s₁
mapFin n≤m (`if s then s₁ else s₂) = `if mapFin n≤m s then mapFin n≤m s₁ else mapFin n≤m s₂
mapFin n≤m ∣ s ∣                   = ∣ mapFin n≤m s ∣
mapFin n≤m (hash s)                = hash (mapFin n≤m s)
mapFin n≤m (versig x x₁)           = versig x (map (flip F.inject≤ n≤m) x₁)
mapFin n≤m (absAfter x ⇒ s)        = absAfter x ⇒ mapFin n≤m s
mapFin n≤m (relAfter x ⇒ s)        = relAfter x ⇒ mapFin n≤m s

⋁ : List (∃[ ctx ] Script ctx `Bool) → ∃[ ctx′ ] Script ctx′ `Bool
⋁ []       = Ctx 0 , `true
⋁ (s ∷ []) = s
⋁ ((Ctx n , x) ∷ xs)
  with ⋁ xs
... | Ctx m , y
  with n ≤? m
... | yes n≤m = _ , (mapFin n≤m x `∨ y)
... | no  n≰m = _ , (x `∨ mapFin (Nat.≰⇒≥ n≰m) y)

⋀ : List (Script ctx `Bool) → Script ctx `Bool
-- ⋀ = foldr _`∧_ `true
⋀ []       = `true
⋀ (s ∷ []) = s
⋀ (s ∷ ss) = s `∧ ⋀ ss
