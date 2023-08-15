------------------------------------------------------------------------
-- Semantics of transactions.
------------------------------------------------------------------------
module Bitcoin.Tx.Semantics where

open import Prelude.Init; open SetAsType
open import Prelude.ToN
open import Prelude.DecEq
open import Prelude.Ord
open import Prelude.Num

open import Bitcoin.BasicTypes
-------------------------- ** for fast evaluation ** ---------------------------------
  hiding (date∶_; _days; _days≤)
private date∶_/_/_ = Op₃ ℕ ∋ const ∘ const
        _days      = id
        _days≤     = λ {m} → Nat.m≤m+n m ∘ _days
--------------------------------------------------------------------------------------
open import Bitcoin.Crypto
open import Bitcoin.Script.Base
open import Bitcoin.Script.Semantics
open import Bitcoin.Tx.Base
open import Bitcoin.Tx.Crypto

-- Output redeeming.
record _,_,_↝[_]_,_,_ (tx : Tx i o)    (j : Fin o)   (t : Time)
                      (v : Value)
                      (tx′ : Tx i′ o′) (j′ : Fin i′) (t′ : Time) : Type where
  field

    ⦃ witness~validator ⦄ :
      (tx ‼ᵒ j) .proj₁ ≡ (tx′ ‼ʷ j′) .proj₁

    ---------------------------------------------------------------

    input~output :
      tx′ ‼ⁱ j′ ≡ tx ♯at j

    scriptValidates :
      tx′ , j′ ⊨ (tx ‼ᵒ j) ∙validator

    value≡ :
      v ≡ (tx ‼ᵒ j) ∙value

    satisfiesAbsLock :
      t′ ≥ tx′ .absLock

    satisfiesRelLock :
        (t′ ≥ t)
      × (t′ ∸ t ≥ tx′ ‼ʳ j′)

open _,_,_↝[_]_,_,_ public

_,_,_↛_,_,_ : Tx i o → Fin o → Time → Tx i′ o′ → Fin i′ → Time → Type
tx , j , t ↛ tx′ , j′ , t′ = ¬ (∃[ v ] (tx , j , t ↝[ v ] tx′ , j′ , t′))

module Example3 {k k′ : KeyPair} {v₀ v₁ : Value} where

  t₀ = date∶ 2 / 1 / 2017
  t₁ = date∶ 6 / 1 / 2017

  T₀ : Tx 0 1
  T₀ = record
    { inputs  = []
    ; wit     = []
    ; relLock = []
    ; outputs = [ v₀ redeemable-by k ]
    ; absLock = t₀ }

  T₁ : Tx 1 1
  T₁ = sig⋆ [ [ k ] ] record
    { inputs  = [ (T₀ ♯) at 0 ]
    ; wit     = wit⊥
    ; relLock = [ 0 ]
    ; outputs = [ v₁ redeemable-by k′ ]
    ; absLock = t₁ }

  T₁′ : Tx 1 1
  T₁′ = sig⋆ [ [ k ] ] record
    { inputs  = [ (T₀ ♯) at 0 ]
    ; wit     = wit⊥
    ; relLock = [ 2 days ]
    ; outputs = [ v₁ redeemable-by k′ ]
    ; absLock = date∶ 5 / 1 / 2017 }

  T₀↝T₁ : T₀ , 0 , t₀ ↝[ v₀ ] T₁ , 0 , t₁
  T₀↝T₁ = record
    { input~output     = refl
    ; scriptValidates  = ver⋆sig≡ T₁ 0
    ; value≡           = refl
    ; satisfiesAbsLock = ≤-refl
    ; satisfiesRelLock = 4 days≤ , z≤n
    }

  T₀↝T₁′ : T₀ , 0 , t₀ ↝[ v₀ ] T₁′ , 0 , t₁
  T₀↝T₁′ = record
    { input~output     = refl
    ; scriptValidates  = ver⋆sig≡ T₁′ 0
    ; value≡           = refl
    ; satisfiesAbsLock = 1 days≤
    ; satisfiesRelLock = 4 days≤ , 2 days≤
    }

module Example4 {k k₂ : KeyPair} {t t′ : Time} (t≤t′ : t ≤ t′) where

  T₁′ : Tx 0 1
  T₁′ = record
    { inputs  = []
    ; wit     = []
    ; relLock = []
    ; outputs = [ 1 redeemable-by k ]
    ; absLock = t }

  T₂′ : Tx 0 1
  T₂′ = record
    { inputs  = []
    ; wit     = []
    ; relLock = []
    ; outputs = [ 2 redeemable-by k ]
    ; absLock = t }

  T₃′ : Tx 2 1
  T₃′ = sig⋆ [ [ k ] ⨾ [ k ] ] record
    { inputs  = [ (T₁′ ♯) at 0 ⨾ (T₂′ ♯) at 0 ]
    ; wit     = wit⊥
    ; relLock = [ 0            ⨾ 0            ]
    ; outputs = [ 3 redeemable-by k₂ ]
    ; absLock = t′ }

  T₁′↝T₃′ : T₁′ , 0 , t ↝[ 1 ] T₃′ , 0 , t′
  T₁′↝T₃′ = record
    { input~output     = refl
    ; scriptValidates  = ver⋆sig≡ T₃′ 0
    ; value≡           = refl
    ; satisfiesAbsLock = ≤-refl
    ; satisfiesRelLock = t≤t′ , z≤n
    }

  T₂′↝T₃′ : T₂′ , 0 , t ↝[ 2 ] T₃′ , 1 , t′
  T₂′↝T₃′ = record
    { input~output     = refl
    ; scriptValidates  = ver⋆sig≡ T₃′ 1
    ; value≡           = refl
    ; satisfiesAbsLock = ≤-refl
    ; satisfiesRelLock = t≤t′ , z≤n
    }

  T₃″ : Tx 2 1
  T₃″ = record T₃′ {wit = [ T₃′ ‼ʷ 0 ⨾ -, [ SIG k (μ T₃′ 0) ] ]}

  T₂′↛T₃″ : T₂′ , 0 , t ↛ T₃″ , 1 , t′
  T₂′↛T₃″ (_ , record {scriptValidates = ver≡})
    = ⊨-elim T₃″ 1F _ ver≡ $ false⇒¬T $
    begin
      ver⋆ [ k ] [ SIG k (μ T₃′ 0) ] T₃″ 1
    ≡⟨ if-eta _ ⟩
      VER k (SIG k _) _
    ≡⟨ ¬T⇒false $ VERSIG≢′ (λ ()) ⟩
      false
    ∎ where open ≡-Reasoning; open import Prelude.General
