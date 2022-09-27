------------------------------------------------------------------------
-- Hashing/signing transactions.
------------------------------------------------------------------------
module Bitcoin.Tx.Crypto where

open import Data.Vec using (_[_]≔_)

open import Prelude.Init
open import Prelude.Functor
open import Prelude.ToN
open import Prelude.Bitstring

open import Bitcoin.BasicTypes
open import Bitcoin.Crypto
open import Bitcoin.Tx.Base
open import Bitcoin.Script.Base

-- Remove witnesses (i.e. adhere to SegregatedWitness feature of Bitcoin)
wit⊥ : ∀ {n} → Vec ∃Witness n
wit⊥ = V.replicate (_ , [])

wit→⊥ : Tx i o → Tx i o
wit→⊥ tx = record tx { wit = wit⊥ }

-- Sign a transaction
μ : Tx i o → Fin i → Tx i o
μ {i = suc _} tx i′ = record tx { wit = wit⊥ [ 0F ]≔ (_ , V.[ + (toℕ i′) ]) }

sig : List KeyPair → Tx i o → Fin i → Tx i o
sig ks tx i = record tx { wit = wit tx [ i ]≔ (_ , V.fromList (flip SIG (μ tx i) <$> ks)) }

sig⋆ : Vec (List KeyPair) i → Tx i o → Tx i o
sig⋆ kss tx = record tx { wit = (λ i → _ , (V.fromList (flip SIG (μ tx i) <$> V.lookup kss i))) <$> V.allFin _ }

-- m-of-n multi-signature scheme
ver : KeyPair → HashId → Tx i o → Fin i → Bool
ver k σ tx i = VER k σ (μ tx i)

ver⋆ : List KeyPair → List HashId → Tx i o → Fin i → Bool
ver⋆ _         []      _ _ = true
ver⋆ []        _       _ _ = false
ver⋆ (k ∷ ks) (σ ∷ σs) T i = if ver k σ T i then ver⋆ ks σs T i else ver⋆ (k ∷ ks) σs T i

hashTxⁱ : TxInput′ → TxInput
hashTxⁱ (tx at i) = (tx ♯) at (toℕ i)
