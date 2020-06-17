------------------------------------------------------------------------
-- Semantics of transactions.
------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}
module Bitcoin.Tx.Semantics where

open import Data.Bool     using (Bool; true)
open import Data.Nat      using (_∸_; _≥_)
open import Data.Product  using (_×_; _,_; proj₁; proj₂; ∃-syntax)
open import Data.List     using (List; [_])
open import Data.Vec as V using ()
open import Data.Fin as F using (Fin; toℕ)
  renaming (zero to 0F)

open import Relation.Nullary                      using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Bitcoin.BasicTypes
open import Bitcoin.Crypto
open import Bitcoin.Script.Base
open import Bitcoin.Script.Semantics
open import Bitcoin.Tx.Base
open import Bitcoin.Tx.Crypto

-- Output redeeming.
record _,_,_↝[_]_,_,_ (tx : Tx i o) (i : Fin o) (t : Time)
                      (v : Value)
                      (tx′ : Tx i′ o′) (j : Fin i′) (t′ : Time)
                      : Set where
  field

    witness~validator :
      proj₁ (tx ‼ᵒ i) ≡ Ctx (proj₁ (tx′ ‼ʷ j))

    ---------------------------------------------------------------

    input~output :
      tx′ ‼ⁱ j ≡ record { txId = hashTx (_ , _ , tx) ; index = toℕ i }

    scriptValidates :
      (tx′ , j ⊨ validator (proj₂ (tx ‼ᵒ i))) {pr = witness~validator}

    value≡ :
      v ≡ value (proj₂ (tx ‼ᵒ i))

    satisfiesAbsLock :
      t′ ≥ absLock tx′

    satisfiesRelLock :
        (t′ ≥ t)
      × (t′ ∸ t ≥ tx′ ‼ʳ j)


_,_,_↛_,_,_ : Tx i o → Fin o → Time → Tx i′ o′ → Fin i′ → Time → Set
tx , i , t ↛ tx′ , j , t′ = ¬ ∃[ v ] (tx , i , t ↝[ v ] tx′ , j , t′)

module Example4 where

  postulate
    ks ks′ : List KeyPair
    v₀ v₁ : Value
    t₀ t₁ abs₀ rel₀ : Time

  T₀ : Tx 0 1
  T₀ = record
         { inputs = V.[]
         ; wit = V.[]
         ; relLock = V.[]
         ; outputs = V.[ Ctx 1 , (record { value = v₀ ; validator = ƛ (versig ks [ 0F ]) }) ]
         ; absLock = abs₀ }

  T₁ : Tx 1 1
  T₁ = sig⋆ V.[ ks ]
            (record { inputs  = V.[ record { txId = hashTx (_ , _ , T₀) ; index = 0 } ]
                    ; wit     = wit⊥
                    ; relLock = V.[ rel₀ ]
                    ; outputs = V.[ Ctx 1 , (record { value = v₁ ; validator = ƛ (versig ks′ [ 0F ]) }) ]
                    ; absLock = t₁ })

  T₁′ : Tx 1 1
  T₁′ = sig⋆ V.[ ks′ ]
             (record { inputs = V.[ record { txId = hashTx (_ , _ , T₀) ; index = 0 } ]
                     ; wit     = wit⊥
                     ; relLock = V.[ 1 ]
                     ; outputs = V.[ Ctx 1 , (record { value = v₁ ; validator = ƛ (versig ks′ [ 0F ]) }) ]
                     ; absLock = t₁ })

  T₀↝T₁ : T₀ , 0F , t₀ ↝[ v₀ ] T₁ , 0F , t₁
  T₀↝T₁ = {!!}

  T₀↝T₁′ : T₀ , 0F , t₀ ↝[ v₀ ] T₁′ , 0F , t₁
  T₀↝T₁′ = {!!}
