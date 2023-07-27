------------------------------------------------------------------------
-- Semantics of transactions.
------------------------------------------------------------------------
module Bitcoin.Tx.Semantics where

open import Prelude.Init; open SetAsType
open import Prelude.ToN
open import Prelude.DecEq
open import Prelude.Ord

open import Bitcoin.BasicTypes
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

  open Nat using (m≤m+n)

  t₀ = date∶ 2 / 1 / 2017
  t₁ = date∶ 6 / 1 / 2017

  T₀ : Tx 0 1
  T₀ = record
    { inputs  = []
    ; wit     = []
    ; relLock = []
    ; outputs = [ 1 , v₀ locked-by ƛ versig [ k ] [ 0F ] ]
    ; absLock = t₀ }

  T₁ : Tx 1 1
  T₁ = sig⋆ [ [ k ] ] record
    { inputs  = [ (T₀ ♯) at 0 ]
    ; wit     = wit⊥
    ; relLock = [ 0 ]
    ; outputs = [ 1 , v₁ locked-by ƛ versig [ k′ ] [ 0F ] ]
    ; absLock = t₁ }

  T₁′ : Tx 1 1
  T₁′ = sig⋆ [ [ k ] ] record
    { inputs  = [ (T₀ ♯) at 0 ]
    ; wit     = wit⊥
    ; relLock = [ 2 days ]
    ; outputs = [ 1 , v₁ locked-by ƛ versig [ k′ ] [ 0F ] ]
    ; absLock = date∶ 5 / 1 / 2017 }

  T₀↝T₁ : T₀ , 0F , t₀ ↝[ v₀ ] T₁ , 0F , t₁
  T₀↝T₁ = record
    { input~output     = refl
    ; scriptValidates  = ver⋆sig≡ T₁ 0F
    ; value≡           = refl
    ; satisfiesAbsLock = ≤-refl
    ; satisfiesRelLock = m≤m+n _ (4 days) , z≤n
    }

  T₀↝T₁′ : T₀ , 0F , t₀ ↝[ v₀ ] T₁′ , 0F , t₁
  T₀↝T₁′ = record
    { input~output     = refl
    ; scriptValidates  = ver⋆sig≡ T₁′ 0F
    ; value≡           = refl
    ; satisfiesAbsLock = m≤m+n _ (1 days)
    ; satisfiesRelLock = m≤m+n _ (4 days) , m≤m+n _ (2 days)
    }

module Example4 {k k₂ : KeyPair} {t t′ : Time} (t≤t′ : t ≤ t′) where

  open import Prelude.General

  T₁′ : Tx 0 1
  T₁′ = record
    { inputs  = []
    ; wit     = []
    ; relLock = []
    ; outputs = [ 1 , 1 locked-by ƛ versig [ k ] [ 0F ] ]
    ; absLock = t }

  T₂′ : Tx 0 1
  T₂′ = record
    { inputs  = []
    ; wit     = []
    ; relLock = []
    ; outputs = [ 1 , 2 locked-by ƛ versig [ k ] [ 0F ] ]
    ; absLock = t }

  T₃′ : Tx 2 1
  T₃′ = sig⋆ [ [ k ] ⨾ [ k ] ] record
    { inputs  = [ (T₁′ ♯) at 0 ⨾ (T₂′ ♯) at 0 ]
    ; wit     = wit⊥
    ; relLock = [ 0            ⨾ 0            ]
    ; outputs = [ 1 , 3 locked-by ƛ versig [ k₂ ] [ 0F ] ]
    ; absLock = t′ }

  T₁′↝T₃′ : T₁′ , 0F , t ↝[ 1 ] T₃′ , 0F , t′
  T₁′↝T₃′ = record
    { input~output     = refl
    ; scriptValidates  = ver⋆sig≡ T₃′ 0F
    ; value≡           = refl
    ; satisfiesAbsLock = ≤-refl
    ; satisfiesRelLock = t≤t′ , z≤n
    }

  T₂′↝T₃′ : T₂′ , 0F , t ↝[ 2 ] T₃′ , 1F , t′
  T₂′↝T₃′ = record
    { input~output     = refl
    ; scriptValidates  = ver⋆sig≡ T₃′ 1F
    ; value≡           = refl
    ; satisfiesAbsLock = ≤-refl
    ; satisfiesRelLock = t≤t′ , z≤n
    }

  T₃″ : Tx 2 1
  T₃″ = record T₃′ {wit = [ T₃′ ‼ʷ 0F ⨾ -, [ SIG k (μ T₃′ 0F) ] ]}

  T₂′↛T₃″ : T₂′ , 0F , t ↛ T₃″ , 1F , t′
  T₂′↛T₃″ (_ , record {scriptValidates = ver≡})
    = ⊨-elim T₃″ 1F _ ver≡ $ false⇒¬T $
    begin
      ver⋆ [ k ] [ SIG k (μ T₃′ 0F) ] T₃″ 1F
    ≡⟨ if-eta _ ⟩
      VER k (SIG k _) _
    ≡⟨ ¬T⇒false $ VERSIG≢′ (λ ()) ⟩
      false
    ∎ where open ≡-Reasoning
