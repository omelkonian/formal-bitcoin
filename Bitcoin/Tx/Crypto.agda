------------------------------------------------------------------------
-- Hashing/signing transactions.
------------------------------------------------------------------------
module Bitcoin.Tx.Crypto where

open import Function using (flip)

open import Data.Bool     using (Bool; true; false; if_then_else_)
open import Data.Product  using (_,_)
open import Data.Nat      using (suc)
open import Data.Integer  using (ℤ; +_)
open import Data.Fin      using (Fin; toℕ)
  renaming (zero to 0F; suc to FS)
open import Data.List     using (List; []; _∷_; map)
open import Data.Vec as V using (Vec; _[_]≔_; lookup; allFin)

open import Bitcoin.BasicTypes
open import Bitcoin.Crypto
open import Bitcoin.Tx.Base

-- Remove witnesses (i.e. adhere to SegregatedWitness feature of Bitcoin)
wit⊥ : ∀ {n} → Vec ∃Witness n
wit⊥ = V.replicate (_ , V.[])

wit→⊥ : Tx i o → Tx i o
wit→⊥ tx = record tx { wit = wit⊥ }

-- Hash a transaction (i.e. get its identifier)
hashTx : Tx i o → ℤ
hashTx tx = HASH (wit→⊥ tx)

-- Sign a transaction
μ : Tx i o → Fin i → Tx i o
μ {i = suc _} tx i′ = record tx { wit = wit⊥ [ 0F ]≔ (_ , V.[ + (toℕ i′) ]) }

sig : List KeyPair → Tx i o → Fin i → Tx i o
sig ks tx i = record tx { wit = wit tx [ i ]≔ (_ , V.fromList (map (flip SIG (μ tx i)) ks)) }

sig⋆ : Vec (List KeyPair) i → Tx i o → Tx i o
sig⋆ kss tx = record tx { wit = V.map (λ i → _ , (V.fromList (map (flip SIG (μ tx i)) (lookup kss i)))) (allFin _) }

-- m-of-n multi-signature scheme
ver : KeyPair → ℤ → Tx i o → Fin i → Bool
ver k σ tx i = VER k σ (μ tx i)

ver⋆ : List KeyPair → List ℤ → Tx i o → Fin i → Bool
ver⋆ _         []        _ _ = true
ver⋆ []        _         _ _ = false
ver⋆ (k ∷ ks) (σ ∷ σs) T i = if ver k σ T i then ver⋆ ks σs T i else ver⋆ (k ∷ ks) σs T i
