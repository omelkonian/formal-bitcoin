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
record _,_,_↝[_]_,_,_ (tx : Tx i o) (i : Fin o) (t : Time)
                      (v : Value)
                      (tx′ : Tx i′ o′) (j : Fin i′) (t′ : Time) : Type where
  field

    ⦃ witness~validator ⦄ :
      (tx ‼ᵒ i) .proj₁ ≡ (tx′ ‼ʷ j) .proj₁

    ---------------------------------------------------------------

    input~output :
      tx′ ‼ⁱ j ≡ tx ♯at i

    scriptValidates :
      tx′ , j ⊨ (tx ‼ᵒ i) ∙validator

    value≡ :
      v ≡ (tx ‼ᵒ i) ∙value

    satisfiesAbsLock :
      t′ ≥ tx′ .absLock

    satisfiesRelLock :
        (t′ ≥ t)
      × (t′ ∸ t ≥ tx′ ‼ʳ j)

_,_,_↛_,_,_ : Tx i o → Fin o → Time → Tx i′ o′ → Fin i′ → Time → Type
tx , i , t ↛ tx′ , j , t′ = ¬ (∃[ v ] (tx , i , t ↝[ v ] tx′ , j , t′))

module Example4 where

  postulate
    ks ks′ : List KeyPair
    v₀ v₁ : Value
    t₀ t₁ abs₀ rel₀ : Time

  T₀ : Tx 0 1
  T₀ = record
    { inputs  = []
    ; wit     = []
    ; relLock = []
    ; outputs = V.[ 1 , (v₀ locked-by ƛ (versig ks [ 0F ])) ]
    ; absLock = abs₀ }

  T₁ : Tx 1 1
  T₁ = sig⋆ V.[ ks ] record
    { inputs  = V.[ (T₀ ♯) at 0 ]
    ; wit     = wit⊥
    ; relLock = V.[ rel₀ ]
    ; outputs = V.[ 1 , (v₁ locked-by ƛ (versig ks′ [ 0F ])) ]
    ; absLock = t₁ }

  T₁′ : Tx 1 1
  T₁′ = sig⋆ V.[ ks′ ] record
    { inputs = V.[ (T₀ ♯) at 0 ]
    ; wit     = wit⊥
    ; relLock = V.[ 1 ]
    ; outputs = V.[ 1 , (v₁ locked-by ƛ (versig ks′ [ 0F ])) ]
    ; absLock = t₁ }

  postulate
    T₀↝T₁ : T₀ , 0F , t₀ ↝[ v₀ ] T₁ , 0F , t₁
    T₀↝T₁′ : T₀ , 0F , t₀ ↝[ v₀ ] T₁′ , 0F , t₁
