------------------------------------------------------------------------
-- Decidable equality for Bitcoin scripts.
------------------------------------------------------------------------
module Bitcoin.Script.DecidableEquality where

open import Data.Product using (_,_)
open import Data.Bool    using (Bool)
open import Data.Nat     using ()
  renaming (_≟_ to _≟ℕ_)
open import Data.Fin     using (Fin)
  renaming (_≟_ to _≟ᶠ_)
open import Data.Integer using (ℤ)
  renaming (_≟_ to _≟ℤ_)

open import Data.List.Relation.Binary.Equality.DecPropositional using (_≡?_)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Bitcoin.Crypto
open import Bitcoin.Script.Base

import Prelude.Set' as SET

-- Sets of public-private key pairs.
_≟ₖ_ : Decidable {A = KeyPair} _≡_
x ≟ₖ y with pub x ≟ℤ pub y | sec x ≟ℤ sec y
... | no ¬p    | _        = no λ{ refl → ¬p refl }
... | _        | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl | yes refl = yes refl

_≟ᶜ_ : Decidable {A = ScriptContext} _≡_
(Ctx n) ≟ᶜ (Ctx n′)
  with n ≟ℕ n′
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl

-- Sets of Bitcoin scripts
-- postulate
_≟∃ₛ_ : Decidable {A = ∃Script} _≡_
(n , .`ℤ , var x) ≟∃ₛ (n′ , .`ℤ , var x₁)
  with n ≟ᶜ n′
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x ≟ᶠ x₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
(n , .`ℤ , var x) ≟∃ₛ (n′ , .`ℤ , ` x₁) = no λ ()
(n , .`ℤ , var x) ≟∃ₛ (n′ , .`ℤ , (s′ `+ s′₁)) = no λ ()
(n , .`ℤ , var x) ≟∃ₛ (n′ , .`ℤ , (s′ `- s′₁)) = no λ ()
(n , .`ℤ , var x) ≟∃ₛ (n′ , .`Bool , (s′ `= s′₁)) = no λ ()
(n , .`ℤ , var x) ≟∃ₛ (n′ , .`Bool , (s′ `< s′₁)) = no λ ()
(n , .`ℤ , var x) ≟∃ₛ (n′ , ty′ , (`if s′ then s′₁ else s′₂)) = no λ ()
(n , .`ℤ , var x) ≟∃ₛ (n′ , .`ℤ , ∣ s′ ∣) = no λ ()
(n , .`ℤ , var x) ≟∃ₛ (n′ , .`ℤ , hash s′) = no λ ()
(n , .`ℤ , var x) ≟∃ₛ (n′ , .`Bool , versig _ x₁) = no λ ()
(n , .`ℤ , var x) ≟∃ₛ (n′ , ty′ , (absAfter x₁ ⇒ s′)) = no λ ()
(n , .`ℤ , var x) ≟∃ₛ (n′ , ty′ , (relAfter x₁ ⇒ s′)) = no λ ()

(n , .`ℤ , ` x) ≟∃ₛ (n′ , .`ℤ , var x₁) = no λ ()
(n , .`ℤ , ` x) ≟∃ₛ (n′ , .`ℤ , ` x₁)
  with n ≟ᶜ n′
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x ≟ℤ x₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
(n , .`ℤ , ` x) ≟∃ₛ (n′ , .`ℤ , (s′ `+ s′₁)) = no λ ()
(n , .`ℤ , ` x) ≟∃ₛ (n′ , .`ℤ , (s′ `- s′₁)) = no λ ()
(n , .`ℤ , ` x) ≟∃ₛ (n′ , .`Bool , (s′ `= s′₁)) = no λ ()
(n , .`ℤ , ` x) ≟∃ₛ (n′ , .`Bool , (s′ `< s′₁)) = no λ ()
(n , .`ℤ , ` x) ≟∃ₛ (n′ , ty′ , (`if s′ then s′₁ else s′₂)) = no λ ()
(n , .`ℤ , ` x) ≟∃ₛ (n′ , .`ℤ , ∣ s′ ∣) = no λ ()
(n , .`ℤ , ` x) ≟∃ₛ (n′ , .`ℤ , hash s′) = no λ ()
(n , .`ℤ , ` x) ≟∃ₛ (n′ , .`Bool , versig _ x₁) = no λ ()
(n , .`ℤ , ` x) ≟∃ₛ (n′ , ty′ , (absAfter x₁ ⇒ s′)) = no λ ()
(n , .`ℤ , ` x) ≟∃ₛ (n′ , ty′ , (relAfter x₁ ⇒ s′)) = no λ ()

(n , .`ℤ , (s `+ s₁)) ≟∃ₛ (n′ , .`ℤ , var x) = no λ ()
(n , .`ℤ , (s `+ s₁)) ≟∃ₛ (n′ , .`ℤ , ` x) = no λ ()
(n , .`ℤ , (s `+ s₁)) ≟∃ₛ (n′ , .`ℤ , (s′ `+ s′₁))
  with (n , `ℤ , s) ≟∃ₛ (n′ , `ℤ , s′) | (n , `ℤ , s₁) ≟∃ₛ (n′ , `ℤ , s′₁)
... | no ¬p     | _        = no λ{ refl → ¬p refl }
... | _         | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl  | yes refl = yes refl
(n , .`ℤ , (s `+ s₁)) ≟∃ₛ (n′ , .`ℤ , (s′ `- s′₁)) = no λ ()
(n , .`ℤ , (s `+ s₁)) ≟∃ₛ (n′ , .`Bool , (s′ `= s′₁)) = no λ ()
(n , .`ℤ , (s `+ s₁)) ≟∃ₛ (n′ , .`Bool , (s′ `< s′₁)) = no λ ()
(n , .`ℤ , (s `+ s₁)) ≟∃ₛ (n′ , ty′ , (`if s′ then s′₁ else s′₂)) = no λ ()
(n , .`ℤ , (s `+ s₁)) ≟∃ₛ (n′ , .`ℤ , ∣ s′ ∣) = no λ ()
(n , .`ℤ , (s `+ s₁)) ≟∃ₛ (n′ , .`ℤ , hash s′) = no λ ()
(n , .`ℤ , (s `+ s₁)) ≟∃ₛ (n′ , .`Bool , versig _ x) = no λ ()
(n , .`ℤ , (s `+ s₁)) ≟∃ₛ (n′ , ty′ , (absAfter x ⇒ s′)) = no λ ()
(n , .`ℤ , (s `+ s₁)) ≟∃ₛ (n′ , ty′ , (relAfter x ⇒ s′)) = no λ ()

(n , .`ℤ , (s `- s₁)) ≟∃ₛ (n′ , .`ℤ , var x) = no λ ()
(n , .`ℤ , (s `- s₁)) ≟∃ₛ (n′ , .`ℤ , ` x) = no λ ()
(n , .`ℤ , (s `- s₁)) ≟∃ₛ (n′ , .`ℤ , (s′ `+ s′₁)) = no λ ()
(n , .`ℤ , (s `- s₁)) ≟∃ₛ (n′ , .`ℤ , (s′ `- s′₁))
  with (n , `ℤ , s) ≟∃ₛ (n′ , `ℤ , s′) | (n , `ℤ , s₁) ≟∃ₛ (n′ , `ℤ , s′₁)
... | no ¬p     | _        = no λ{ refl → ¬p refl }
... | _         | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl  | yes refl = yes refl
(n , .`ℤ , (s `- s₁)) ≟∃ₛ (n′ , .`Bool , (s′ `= s′₁)) = no λ ()
(n , .`ℤ , (s `- s₁)) ≟∃ₛ (n′ , .`Bool , (s′ `< s′₁)) = no λ ()
(n , .`ℤ , (s `- s₁)) ≟∃ₛ (n′ , ty′ , (`if s′ then s′₁ else s′₂)) = no λ ()
(n , .`ℤ , (s `- s₁)) ≟∃ₛ (n′ , .`ℤ , ∣ s′ ∣) = no λ ()
(n , .`ℤ , (s `- s₁)) ≟∃ₛ (n′ , .`ℤ , hash s′) = no λ ()
(n , .`ℤ , (s `- s₁)) ≟∃ₛ (n′ , .`Bool , versig _ x) = no λ ()
(n , .`ℤ , (s `- s₁)) ≟∃ₛ (n′ , ty′ , (absAfter x ⇒ s′)) = no λ ()
(n , .`ℤ , (s `- s₁)) ≟∃ₛ (n′ , ty′ , (relAfter x ⇒ s′)) = no λ ()

(n , .`Bool , (s `= s₁)) ≟∃ₛ (n′ , .`ℤ , var x) = no λ ()
(n , .`Bool , (s `= s₁)) ≟∃ₛ (n′ , .`ℤ , ` x) = no λ ()
(n , .`Bool , (s `= s₁)) ≟∃ₛ (n′ , .`ℤ , (s′ `+ s′₁)) = no λ ()
(n , .`Bool , (s `= s₁)) ≟∃ₛ (n′ , .`ℤ , (s′ `- s′₁)) = no λ ()
(n , .`Bool , (s `= s₁)) ≟∃ₛ (n′ , .`Bool , (s′ `= s′₁))
  with (n , `ℤ , s) ≟∃ₛ (n′ , `ℤ , s′) | (n , `ℤ , s₁) ≟∃ₛ (n′ , `ℤ , s′₁)
... | no ¬p     | _        = no λ{ refl → ¬p refl }
... | _         | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl  | yes refl = yes refl
(n , .`Bool , (s `= s₁)) ≟∃ₛ (n′ , .`Bool , (s′ `< s′₁)) = no λ ()
(n , .`Bool , (s `= s₁)) ≟∃ₛ (n′ , ty′ , (`if s′ then s′₁ else s′₂)) = no λ ()
(n , .`Bool , (s `= s₁)) ≟∃ₛ (n′ , .`ℤ , ∣ s′ ∣) = no λ ()
(n , .`Bool , (s `= s₁)) ≟∃ₛ (n′ , .`ℤ , hash s′) = no λ ()
(n , .`Bool , (s `= s₁)) ≟∃ₛ (n′ , .`Bool , versig _ x) = no λ ()
(n , .`Bool , (s `= s₁)) ≟∃ₛ (n′ , ty′ , (absAfter x ⇒ s′)) = no λ ()
(n , .`Bool , (s `= s₁)) ≟∃ₛ (n′ , ty′ , (relAfter x ⇒ s′)) = no λ ()

(n , .`Bool , (s `< s₁)) ≟∃ₛ (n′ , .`ℤ , var x) = no λ ()
(n , .`Bool , (s `< s₁)) ≟∃ₛ (n′ , .`ℤ , ` x) = no λ ()
(n , .`Bool , (s `< s₁)) ≟∃ₛ (n′ , .`ℤ , (s′ `+ s′₁)) = no λ ()
(n , .`Bool , (s `< s₁)) ≟∃ₛ (n′ , .`ℤ , (s′ `- s′₁)) = no λ ()
(n , .`Bool , (s `< s₁)) ≟∃ₛ (n′ , .`Bool , (s′ `= s′₁)) = no λ ()
(n , .`Bool , (s `< s₁)) ≟∃ₛ (n′ , .`Bool , (s′ `< s′₁))
  with (n , `ℤ , s) ≟∃ₛ (n′ , `ℤ , s′) | (n , `ℤ , s₁) ≟∃ₛ (n′ , `ℤ , s′₁)
... | no ¬p     | _        = no λ{ refl → ¬p refl }
... | _         | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl  | yes refl = yes refl
(n , .`Bool , (s `< s₁)) ≟∃ₛ (n′ , ty′ , (`if s′ then s′₁ else s′₂)) = no λ ()
(n , .`Bool , (s `< s₁)) ≟∃ₛ (n′ , .`ℤ , ∣ s′ ∣) = no λ ()
(n , .`Bool , (s `< s₁)) ≟∃ₛ (n′ , .`ℤ , hash s′) = no λ ()
(n , .`Bool , (s `< s₁)) ≟∃ₛ (n′ , .`Bool , versig _ x) = no λ ()
(n , .`Bool , (s `< s₁)) ≟∃ₛ (n′ , ty′ , (absAfter x ⇒ s′)) = no λ ()
(n , .`Bool , (s `< s₁)) ≟∃ₛ (n′ , ty′ , (relAfter x ⇒ s′)) = no λ ()

(n , ty , (`if s then s₁ else s₂)) ≟∃ₛ (n′ , .`ℤ , var x) = no λ ()
(n , ty , (`if s then s₁ else s₂)) ≟∃ₛ (n′ , .`ℤ , ` x) = no λ ()
(n , ty , (`if s then s₁ else s₂)) ≟∃ₛ (n′ , .`ℤ , (s′ `+ s′₁)) = no λ ()
(n , ty , (`if s then s₁ else s₂)) ≟∃ₛ (n′ , .`ℤ , (s′ `- s′₁)) = no λ ()
(n , ty , (`if s then s₁ else s₂)) ≟∃ₛ (n′ , .`Bool , (s′ `= s′₁)) = no λ ()
(n , ty , (`if s then s₁ else s₂)) ≟∃ₛ (n′ , .`Bool , (s′ `< s′₁)) = no λ ()
(n , ty , (`if s then s₁ else s₂)) ≟∃ₛ (n′ , ty′ , (`if s′ then s′₁ else s′₂))
  with (n , `Bool , s) ≟∃ₛ (n′ , `Bool , s′) | (n , ty , s₁) ≟∃ₛ (n′ , ty′ , s′₁) | (n , ty , s₂) ≟∃ₛ (n′ , ty′ , s′₂)
... | no ¬p     | _        | _        = no λ{ refl → ¬p refl }
... | _         | no ¬p    | _        = no λ{ refl → ¬p refl }
... | _         | _        | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl  | yes refl | yes refl = yes refl
(n , ty , (`if s then s₁ else s₂)) ≟∃ₛ (n′ , .`ℤ , ∣ s′ ∣) = no λ ()
(n , ty , (`if s then s₁ else s₂)) ≟∃ₛ (n′ , .`ℤ , hash s′) = no λ ()
(n , ty , (`if s then s₁ else s₂)) ≟∃ₛ (n′ , .`Bool , versig _ x) = no λ ()
(n , ty , (`if s then s₁ else s₂)) ≟∃ₛ (n′ , ty′ , (absAfter x ⇒ s′)) = no λ ()
(n , ty , (`if s then s₁ else s₂)) ≟∃ₛ (n′ , ty′ , (relAfter x ⇒ s′)) = no λ ()

(n , .`ℤ , ∣ s ∣) ≟∃ₛ (n′ , .`ℤ , var x) = no λ ()
(n , .`ℤ , ∣ s ∣) ≟∃ₛ (n′ , .`ℤ , ` x) = no λ ()
(n , .`ℤ , ∣ s ∣) ≟∃ₛ (n′ , .`ℤ , (s′ `+ s′₁)) = no λ ()
(n , .`ℤ , ∣ s ∣) ≟∃ₛ (n′ , .`ℤ , (s′ `- s′₁)) = no λ ()
(n , .`ℤ , ∣ s ∣) ≟∃ₛ (n′ , .`Bool , (s′ `= s′₁)) = no λ ()
(n , .`ℤ , ∣ s ∣) ≟∃ₛ (n′ , .`Bool , (s′ `< s′₁)) = no λ ()
(n , .`ℤ , ∣ s ∣) ≟∃ₛ (n′ , ty′ , (`if s′ then s′₁ else s′₂)) = no λ ()
(n , .`ℤ , ∣ s ∣) ≟∃ₛ (n′ , .`ℤ , ∣ s′ ∣)
  with (n , `ℤ , s) ≟∃ₛ (n′ , `ℤ , s′)
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
(n , .`ℤ , ∣ s ∣) ≟∃ₛ (n′ , .`ℤ , hash s′) = no λ ()
(n , .`ℤ , ∣ s ∣) ≟∃ₛ (n′ , .`Bool , versig _ x) = no λ ()
(n , .`ℤ , ∣ s ∣) ≟∃ₛ (n′ , ty′ , (absAfter x ⇒ s′)) = no λ ()
(n , .`ℤ , ∣ s ∣) ≟∃ₛ (n′ , ty′ , (relAfter x ⇒ s′)) = no λ ()

(n , .`ℤ , hash s) ≟∃ₛ (n′ , .`ℤ , var x) = no λ ()
(n , .`ℤ , hash s) ≟∃ₛ (n′ , .`ℤ , ` x) = no λ ()
(n , .`ℤ , hash s) ≟∃ₛ (n′ , .`ℤ , (s′ `+ s′₁)) = no λ ()
(n , .`ℤ , hash s) ≟∃ₛ (n′ , .`ℤ , (s′ `- s′₁)) = no λ ()
(n , .`ℤ , hash s) ≟∃ₛ (n′ , .`Bool , (s′ `= s′₁)) = no λ ()
(n , .`ℤ , hash s) ≟∃ₛ (n′ , .`Bool , (s′ `< s′₁)) = no λ ()
(n , .`ℤ , hash s) ≟∃ₛ (n′ , ty′ , (`if s′ then s′₁ else s′₂)) = no λ ()
(n , .`ℤ , hash s) ≟∃ₛ (n′ , .`ℤ , ∣ s′ ∣) = no λ ()
(n , .`ℤ , hash s) ≟∃ₛ (n′ , .`ℤ , hash s′)
  with (n , `ℤ , s) ≟∃ₛ (n′ , `ℤ , s′)
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
(n , .`ℤ , hash s) ≟∃ₛ (n′ , .`Bool , versig _ x) = no λ ()
(n , .`ℤ , hash s) ≟∃ₛ (n′ , ty′ , (absAfter x ⇒ s′)) = no λ ()
(n , .`ℤ , hash s) ≟∃ₛ (n′ , ty′ , (relAfter x ⇒ s′)) = no λ ()

(n , .`Bool , versig _ x) ≟∃ₛ (n′ , .`ℤ , var x₁) = no λ ()
(n , .`Bool , versig _ x) ≟∃ₛ (n′ , .`ℤ , ` x₁) = no λ ()
(n , .`Bool , versig _ x) ≟∃ₛ (n′ , .`ℤ , (s′ `+ s′₁)) = no λ ()
(n , .`Bool , versig _ x) ≟∃ₛ (n′ , .`ℤ , (s′ `- s′₁)) = no λ ()
(n , .`Bool , versig _ x) ≟∃ₛ (n′ , .`Bool , (s′ `= s′₁)) = no λ ()
(n , .`Bool , versig _ x) ≟∃ₛ (n′ , .`Bool , (s′ `< s′₁)) = no λ ()
(n , .`Bool , versig _ x) ≟∃ₛ (n′ , ty′ , (`if s′ then s′₁ else s′₂)) = no λ ()
(n , .`Bool , versig _ x) ≟∃ₛ (n′ , .`ℤ , ∣ s′ ∣) = no λ ()
(n , .`Bool , versig _ x) ≟∃ₛ (n′ , .`ℤ , hash s′) = no λ ()
(n , .`Bool , versig k x) ≟∃ₛ (n′ , .`Bool , versig k₁ x₁)
  with n ≟ᶜ n′
... | no ¬p = no λ{ refl → ¬p refl }
... | yes refl
  with _≡?_ _≟ₖ_ k k₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with _≡?_ _≟ᶠ_ x x₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
(n , .`Bool , versig _ x) ≟∃ₛ (n′ , ty′ , (absAfter x₁ ⇒ s′)) = no λ ()
(n , .`Bool , versig _ x) ≟∃ₛ (n′ , ty′ , (relAfter x₁ ⇒ s′)) = no λ ()

(n , ty , (absAfter x ⇒ s)) ≟∃ₛ (n′ , .`ℤ , var x₁) = no λ ()
(n , ty , (absAfter x ⇒ s)) ≟∃ₛ (n′ , .`ℤ , ` x₁) = no λ ()
(n , ty , (absAfter x ⇒ s)) ≟∃ₛ (n′ , .`ℤ , (s′ `+ s′₁)) = no λ ()
(n , ty , (absAfter x ⇒ s)) ≟∃ₛ (n′ , .`ℤ , (s′ `- s′₁)) = no λ ()
(n , ty , (absAfter x ⇒ s)) ≟∃ₛ (n′ , .`Bool , (s′ `= s′₁)) = no λ ()
(n , ty , (absAfter x ⇒ s)) ≟∃ₛ (n′ , .`Bool , (s′ `< s′₁)) = no λ ()
(n , ty , (absAfter x ⇒ s)) ≟∃ₛ (n′ , ty′ , (`if s′ then s′₁ else s′₂)) = no λ ()
(n , ty , (absAfter x ⇒ s)) ≟∃ₛ (n′ , .`ℤ , ∣ s′ ∣) = no λ ()
(n , ty , (absAfter x ⇒ s)) ≟∃ₛ (n′ , .`ℤ , hash s′) = no λ ()
(n , ty , (absAfter x ⇒ s)) ≟∃ₛ (n′ , .`Bool , versig _ x₁) = no λ ()
(n , ty , (absAfter x ⇒ s)) ≟∃ₛ (n′ , ty′ , (absAfter x₁ ⇒ s′))
  with (n , ty , s) ≟∃ₛ (n′ , ty′ , s′)
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x ≟ℕ x₁
... | no ¬p = no λ{ refl → ¬p refl }
... | yes refl = yes refl
(n , ty , (absAfter x ⇒ s)) ≟∃ₛ (n′ , ty′ , (relAfter x₁ ⇒ s′)) = no λ ()

(n , ty , (relAfter x ⇒ s)) ≟∃ₛ (n′ , .`ℤ , var x₁) = no λ ()
(n , ty , (relAfter x ⇒ s)) ≟∃ₛ (n′ , .`ℤ , ` x₁) = no λ ()
(n , ty , (relAfter x ⇒ s)) ≟∃ₛ (n′ , .`ℤ , (s′ `+ s′₁)) = no λ ()
(n , ty , (relAfter x ⇒ s)) ≟∃ₛ (n′ , .`ℤ , (s′ `- s′₁)) = no λ ()
(n , ty , (relAfter x ⇒ s)) ≟∃ₛ (n′ , .`Bool , (s′ `= s′₁)) = no λ ()
(n , ty , (relAfter x ⇒ s)) ≟∃ₛ (n′ , .`Bool , (s′ `< s′₁)) = no λ ()
(n , ty , (relAfter x ⇒ s)) ≟∃ₛ (n′ , ty′ , (`if s′ then s′₁ else s′₂)) = no λ ()
(n , ty , (relAfter x ⇒ s)) ≟∃ₛ (n′ , .`ℤ , ∣ s′ ∣) = no λ ()
(n , ty , (relAfter x ⇒ s)) ≟∃ₛ (n′ , .`ℤ , hash s′) = no λ ()
(n , ty , (relAfter x ⇒ s)) ≟∃ₛ (n′ , .`Bool , versig _ x₁) = no λ ()
(n , ty , (relAfter x ⇒ s)) ≟∃ₛ (n′ , ty′ , (absAfter x₁ ⇒ s′)) = no λ ()
(n , ty , (relAfter x ⇒ s)) ≟∃ₛ (n′ , ty′ , (relAfter x₁ ⇒ s′))
  -- NB: If _≟∃ₛ_ is done after _≟ℕ_ causes Agda to fail termination checking after 2.6.1
  with (n , ty , s) ≟∃ₛ (n′ , ty′ , s′)
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl
  with x ≟ℕ x₁
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl

_≟ₛ_ : Decidable {A = Script ctx ty} _≡_
_≟ₛ_ {ctx = ctx} {ty = ty} x y with (ctx , ty , x) ≟∃ₛ (ctx , ty , y)
... | no ¬p = no λ{ refl → ¬p refl }
... | yes refl = yes refl

_∃≟ₛ_ : Decidable {A = ∃BitcoinScript} _≡_
(n , (ƛ x)) ∃≟ₛ (n′ , (ƛ y))
  with n ≟ᶜ n′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl
  with x ≟ₛ y
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl

module SETₛ = SET {A = ∃BitcoinScript} _∃≟ₛ_

Set⟨∃BitcoinScript⟩ : Set
Set⟨∃BitcoinScript⟩ = Set' where open SETₛ
