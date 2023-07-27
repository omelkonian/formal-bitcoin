------------------------------------------------------------------------
-- Hashing/signing transactions.
------------------------------------------------------------------------
module Bitcoin.Tx.Crypto where

open import Prelude.Init hiding (allFin)
open V using (replicate; _[_]≔_; lookup; allFin)
open import Prelude.General
open import Prelude.Functor
open import Prelude.ToN
open import Prelude.FromList
open import Prelude.Bitstring

open import Bitcoin.BasicTypes
open import Bitcoin.Crypto
open import Bitcoin.Tx.Base
open import Bitcoin.Script.Base

-- Constructing transaction inputs
_♯at_ : Tx i o → Fin o → TxInput
tx ♯at j = (tx ♯) at toℕ j

hashTxⁱ : TxInput′ → TxInput
hashTxⁱ ((_ , _ , tx) at j) = tx ♯at j

-- Remove witnesses (i.e. adhere to SegregatedWitness feature of Bitcoin)
wit⊥ : Vec ∃Witness n
wit⊥ = replicate (-, [])

wit→⊥ : Tx i o → Tx i o
wit→⊥ tx = record tx { wit = wit⊥ }

-- Transaction signatures
μ : Tx i o → Fin i → Tx i o
μ {i = suc _} tx j = record tx { wit = wit⊥ [ 0F ]≔ (-, [ + (toℕ j) ]) }

sig : List KeyPair → Tx i o → Fin i → Tx i o
sig ks tx j = record tx
  { wit = tx .wit [ j ]≔ (-, fromList (flip SIG (μ tx j) <$> ks)) }

ver : KeyPair → HashId → Tx i o → Fin i → Bool
ver k σ tx j = VER k σ (μ tx j)

-- m-of-n multi-signature scheme
sig⋆ : Vec (List KeyPair) i → Tx i o → Tx i o
sig⋆ kss tx = record tx
  { wit = (λ j → -, fromList (flip SIG (μ tx j) <$> lookup kss j)) <$> allFin _ }

ver⋆ : List KeyPair → List HashId → Tx i o → Fin i → Bool
ver⋆ _        []       _ _ = true
ver⋆ []       (_ ∷ _)  _ _ = false
ver⋆ (k ∷ ks) (σ ∷ σs) T j =
  if ver k σ T j then ver⋆ ks σs T j else ver⋆ ks (σ ∷ σs) T j

ver⋆sig≡ : ∀ {k} (t : Tx i o) (j : Fin i) → T $ ver⋆ L.[ k ] L.[ SIG k (μ t j) ] t j
ver⋆sig≡ {k = k} t j rewrite if-eta $ ver k (SIG k (μ t j)) t j = VERSIG≡

module Example1
  (kᵃ kᵇ kᶜ : KeyPair)
  (kᶜ≢kᵇ : kᶜ ≢ kᵇ) (kᶜ≢kᵃ : kᶜ ≢ kᵃ) (kᵇ≢kᵃ : kᵇ ≢ kᵃ)
  (t : Tx (suc i) o)
  where
  σp = SIG kᵃ (μ t 0F)
  σq = SIG kᵇ (μ t 0F)

  ks  = List KeyPair ∋ [ kᶜ ⨾ kᵇ ⨾ kᵃ ]
  σs  = List HashId  ∋ [ σq ⨾ σp ]
  σs′ = List HashId  ∋ [ σp ⨾ σq ]

  -- ** using equational reasoning

  open ≡-Reasoning

  _ : T (ver⋆ ks σs t 0F)
  _ = true⇒T
    $ begin
        ver⋆ ks σs t 0F
      ≡⟨⟩
        (if VER kᶜ σq (μ t 0F) then
          ver⋆ [ kᵇ ⨾ kᵃ ] [ σp ] t 0F
        else
          ver⋆ [ kᵇ ⨾ kᵃ ] [ σq ⨾ σp ] t 0F)
      ≡⟨ if-false $ ¬T⇒false $ VERSIG≢ kᶜ≢kᵇ ⟩
        ver⋆ [ kᵇ ⨾ kᵃ ] σs t 0F
      ≡⟨⟩
        (if VER kᵇ σq (μ t 0F) then
          ver⋆ [ kᵃ ] [ σp ] t 0F
        else
          ver⋆ [ kᵃ ] [ σq ⨾ σp ] t 0F)
      ≡⟨ if-true $ T⇒true VERSIG≡ ⟩
        ver⋆ [ kᵃ ] [ σp ] t 0F
      ≡⟨⟩
        (if VER kᵃ σp (μ t 0F) then
          ver⋆ [] [] t 0F
        else
          ver⋆ [] [ σp ] t 0F)
      ≡⟨ if-true $ T⇒true VERSIG≡ ⟩
        ver⋆ [] [] t 0F
      ≡⟨⟩
        true
      ∎

  _ : ¬ T (ver⋆ ks σs′ t 0F)
  _ = false⇒¬T
    $ begin
        ver⋆ ks σs′ t 0F
      ≡⟨ if-false $ ¬T⇒false $ VERSIG≢ kᶜ≢kᵃ ⟩
        ver⋆ [ kᵇ ⨾ kᵃ ] [ σp ⨾ σq ] t 0F
      ≡⟨ if-false $ ¬T⇒false $ VERSIG≢ kᵇ≢kᵃ ⟩
        ver⋆ [ kᵃ ] [ σp ⨾ σq ] t 0F
      ≡⟨ if-true $ T⇒true VERSIG≡ ⟩
        ver⋆ [] [ σq ] t 0F
      ≡⟨⟩
        false
      ∎

  -- ** using `rewrite`

  _ : T (ver⋆ ks σs t 0F)
  _ rewrite ¬T⇒false $ VERSIG≢ {x = μ t 0F} kᶜ≢kᵇ
          | T⇒true   $ VERSIG≡ {k = kᵇ} {x = μ t 0F}
          | T⇒true   $ VERSIG≡ {k = kᵃ} {x = μ t 0F}
          = tt

  _ : ¬ T (ver⋆ ks σs′ t 0F)
  _ rewrite ¬T⇒false $ VERSIG≢ {x = μ t 0F} kᶜ≢kᵃ
          | ¬T⇒false $ VERSIG≢ {x = μ t 0F} kᵇ≢kᵃ
          | T⇒true   $ VERSIG≡ {k = kᵃ} {x = μ t 0F}
          = id
