------------------------------------------------------------------------
-- Hashing/signing transactions.
------------------------------------------------------------------------
module Bitcoin.Tx.Crypto where

open import Data.Bool     using (Bool; true; false; if_then_else_)
open import Data.Product  using (_,_)
open import Data.Nat      using (suc)
open import Data.Integer  using (ℤ; +_)
open import Data.Fin      using (Fin; toℕ)
  renaming (zero to 0F; suc to FS)
open import Data.List     using (List; []; _∷_)
open import Data.Vec as V using (_[_]≔_)

open import Bitcoin.BasicTypes
open import Bitcoin.Crypto
open import Bitcoin.Tx.Base

-- Remove witnesses (i.e. adhere to SegregatedWitness feature of Bitcoin)
wit→⊥ : Tx i o → Tx i o
wit→⊥ tx = record tx { wit = V.replicate (0 , V.[]) }

-- Hash a transaction (i.e. get its identifier)
hashTx : Tx i o → ℤ
hashTx tx = HASH (wit→⊥ tx)

-- Sign a transaction
μ : Tx i o → Fin i → Tx i o
μ {i = suc _} tx i′ = record tx { wit = (V.replicate (0 , V.[])) [ 0F ]≔ (1 , V.[ + (toℕ i′) ]) }

sig : KeyPair → Tx i o → Fin i → ℤ
sig k tx i = SIG k (μ tx i)

ver : KeyPair → ℤ → Tx i o → Fin i → Bool
ver k σ tx i = VER k σ (μ tx i)

-- m-of-n multi-signature scheme
ver⋆ : List KeyPair → List ℤ → Tx i o → Fin i → Bool
ver⋆ _         []        _ _ = true
ver⋆ []        _         _ _ = false
ver⋆ (k ∷ ks) (σ ∷ σs) T i = if ver k σ T i then ver⋆ ks σs T i else ver⋆ (k ∷ ks) σs T i
