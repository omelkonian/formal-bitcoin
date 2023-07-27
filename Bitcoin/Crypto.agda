------------------------------------------------------------------------
-- Public-key cryptography.
------------------------------------------------------------------------
module Bitcoin.Crypto where

open import Prelude.Init; open SetAsType
open import Prelude.DecEq
open import Prelude.InferenceRules

open import Bitcoin.BasicTypes

record KeyPair : Type where
  field pub : HashId
        sec : HashId
open KeyPair public
unquoteDecl DecEqᵏᵖ = DERIVE DecEq [ quote KeyPair , DecEqᵏᵖ ]

private variable
  A : Type ℓ
  x x′ : A
  k k′ : KeyPair
  σ : HashId

postulate
  -- universal hashing function
  _♯ : ∀ {A : Type ℓ} → A → HashId

  -- signing/verifying
  SIG : KeyPair → A → HashId
  VER : KeyPair → HashId → A → Bool

  VERSIG :
    T (VER k σ x)
    ═════════════
    σ ≡ SIG k x

  SIG-injective :
      (∀ {x : A} → Injective≡ (λ k → SIG k x))
    × (∀ {k} → Injective≡ (λ (x : A) → SIG k x))

VERSIG≡ : T (VER k (SIG k x) x)
VERSIG≡ = VERSIG .proj₂ refl

VERSIG≢ : k ≢ k′ → ¬ T (VER k (SIG k′ x) x)
VERSIG≢ k≢ p = ⊥-elim $ k≢ $ sym $ SIG-injective .proj₁ (VERSIG .proj₁ p)

VERSIG≢′ : x ≢ x′ → ¬ T (VER k (SIG k x) x′)
VERSIG≢′ x≢ p = ⊥-elim $ x≢ $ SIG-injective .proj₂ (VERSIG .proj₁ p)
