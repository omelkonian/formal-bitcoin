------------------------------------------------------------------------
-- Decidable equality for transactions.
------------------------------------------------------------------------
module Bitcoin.Tx.DecidableEquality where

open import Data.Product using (_,_)
open import Data.Nat     using (ℕ)
  renaming (_≟_ to _≟ℕ_)
open import Data.Integer using (ℤ)
  renaming (_≟_ to _≟ℤ_)
open import Data.Fin     using ()
  renaming (_≟_ to _≟ᶠ_)

open import Data.Vec            using (Vec)
open import Data.Vec.Properties using (≡-dec)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Bitcoin.BasicTypes
open import Bitcoin.Script.Base
open import Bitcoin.Script.DecidableEquality
open import Bitcoin.Tx.Base

import Data.Set' as SET

-- Sets of transaction inputs
_≟ᵢ_ : Decidable {A = TxInput} _≡_
x ≟ᵢ y with txId x ≟ℤ txId y | index x ≟ℕ index y
... | no ¬p    | _        = no λ{refl → ¬p refl}
... | _        | no ¬p    = no λ{refl → ¬p refl}
... | yes refl | yes refl = yes refl

module SETᵢ = SET {A = TxInput} _≟ᵢ_

Set⟨TxInput⟩ : Set
Set⟨TxInput⟩ = Set' where open SETᵢ

-- Sets of transaction outputs
_≟ₒ_ : Decidable {A = TxOutput ctx} _≡_
_≟ₒ_ {ctx = ctx} x y with value x ≟ℕ value y | (ctx , validator x) SET∃ₛ.≣ (ctx , validator y)
... | no ¬p    | _        = no λ{refl → ¬p refl}
... | _        | no ¬p′   = no λ{refl → ¬p′ refl}
... | yes refl | yes refl = yes refl

_≟∃ₒ_ : Decidable {A = ∃TxOutput} _≡_
(n , x) ≟∃ₒ (n′ , y)
  with n ≟ᶜ n′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl
  with x ≟ₒ y
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl

module SETₒ = SET {A = ∃TxOutput} _≟∃ₒ_

Set⟨∃TxOutput⟩ : Set
Set⟨∃TxOutput⟩ = Set' where open SETₒ

-- Sets of transactions
_≟∃ʷ_ : Decidable {A = ∃Witness} _≡_
(n , w) ≟∃ʷ (n′ , w′)
  with n ≟ℕ n′
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with ≡-dec _≟ℤ_ w w′
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl

_≟ₜₓ_ : Decidable {A = Tx i o} _≡_
x ≟ₜₓ y with ≡-dec _≟ᵢ_  (inputs x) (inputs y)
           | ≡-dec _≟∃ʷ_ (wit x) (wit y)
           | ≡-dec _≟ℕ_  (relLock x) (relLock y)
           | ≡-dec _≟∃ₒ_ (outputs x) (outputs y)
           | absLock x ≟ℕ absLock y
... | no ¬p    | _        | _        | _        | _        = no λ{refl → ¬p refl}
... | _        | no ¬p′   | _        | _        | _        = no λ{refl → ¬p′ refl}
... | _        | _        | no ¬p′   | _        | _        = no λ{refl → ¬p′ refl}
... | _        | _        | _        | no ¬p′   | _        = no λ{refl → ¬p′ refl}
... | _        | _        | _        | _        | no ¬p′   = no λ{refl → ¬p′ refl}
... | yes refl | yes refl | yes refl | yes refl | yes refl = yes refl

_≟∃ₜₓ_ : Decidable {A = ∃Tx} _≡_
(i , o , tx) ≟∃ₜₓ (i′ , o′ , tx′)
  with i ≟ℕ i′  | o ≟ℕ o′
... | no ¬p    | _        = no λ{refl → ¬p refl}
... | _        | no ¬p    = no λ{refl → ¬p refl}
... | yes refl | yes refl
  with tx ≟ₜₓ tx′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl

module SETₜₓ = SET {A = ∃Tx} _≟∃ₜₓ_

Set⟨Tx⟩ : Set
Set⟨Tx⟩ = Set' where open SETₜₓ

-- Sets of timed transactions
_≟∃ₜₜₓ_ : Decidable {A = TimedTx} _≡_
((i , o , tx) at t) ≟∃ₜₜₓ ((i′ , o′ , tx′) at t′)
  with (i , o , tx) ≟∃ₜₓ (i′ , o′ , tx′) | t ≟ℕ t′
... | no ¬p    | _        = no λ{refl → ¬p refl}
... | _        | no ¬p    = no λ{refl → ¬p refl}
... | yes refl | yes refl = yes refl

module SETₜₜₓ = SET {A = TimedTx} _≟∃ₜₜₓ_

Set⟨TimedTx⟩ : Set
Set⟨TimedTx⟩ = Set' where open SETₜₜₓ
