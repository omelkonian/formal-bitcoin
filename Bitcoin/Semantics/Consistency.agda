------------------------------------------------------------------------
-- Blockchain and consistency.
------------------------------------------------------------------------
-- {-# OPTIONS --allow-unsolved-metas #-}
module Bitcoin.Semantics.Consistency where

open import Function      using (_∘_)
open import Data.Product  using (_,_; proj₁; proj₂; ∃-syntax)
open import Data.Nat      using (zero; suc; _≥_; _<_)
open import Data.Integer  using ()
  renaming (_≟_ to _≟ℤ_)
open import Data.Fin      using (Fin; fromℕ≤)
open import Data.Vec as V using (tabulate; toList; sum)
open import Data.List     using (List; []; _∷_; [_]; map; upTo)
open import Data.List.Membership.Propositional using (_∈_)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Prelude.Lists using (indices)

open import Bitcoin.BasicTypes
open import Bitcoin.Script.Base
open import Bitcoin.Tx.Base
open import Bitcoin.Tx.Crypto
open import Bitcoin.Tx.DecidableEquality
open import Bitcoin.Semantics.Tx

-- Blockchain
Blockchain : Set
Blockchain = List TimedTx -- in reverse chronological order, in contrast to the paper

variable txs txs′ : Blockchain

module _ where
  open SETₜₜₓ hiding (_∈_)

  trans : Blockchain → Set⟨TimedTx⟩
  trans = fromList

  match : Blockchain → HashId → Set⟨TimedTx⟩
  match []                _   = ∅
  match ((tx at t) ∷ txs) tx′ with hashTx (proj₂ (proj₂ tx)) ≟ℤ tx′
  ... | no _  = match txs tx′
  ... | yes _ = singleton (tx at t)
              ∪ match txs tx′

-- UTXO: Unspent transaction outputs.
open SETᵢ

UTXOₜₓ : ∃Tx → Set⟨TxInput⟩
UTXOₜₓ (_ , o , tx) = fromList (map (λ i → hashTx tx at i) (upTo o))

STXOₜₓ : ∃Tx → Set⟨TxInput⟩
STXOₜₓ (_ , _ , tx) = fromList (toList (inputs tx))

UTXO : Blockchain → Set⟨TxInput⟩
UTXO []              = ∅
UTXO (tx at _ ∷ txs) = UTXO txs ─ STXOₜₓ tx
                     ∪ UTXOₜₓ tx

-- Consistent update.
latestTime : Blockchain → Time
latestTime []             = 0
latestTime ((_ at t) ∷ _) = t

record _▷_,_ (txs : Blockchain) (tx : Tx i o) (t : Time) : Set where
  field
    -- well-formedness conditions

    inputsUnique :
      SETᵢ.Unique (toList (inputs tx))

    singleMatch : ∀ (i : Fin i) →
      let
        (tx♯ at _) = tx ‼ⁱ i
      in
        ∃[ tx ] (match txs tx♯ ≡ SETₜₜₓ.singleton tx)

    noOutOfBounds : ∀ (i : Fin i) →
      let
        (Tᵢ♯ at oᵢ)              = tx ‼ⁱ i
        (((_ , o , _) at _) , _) = singleMatch i
      in
        oᵢ < o

    -------------------------------------------------------

    -- (1)
    inputs∈UTXO : ∀ (i : Fin i) →
      let
        (Tᵢ♯ at oᵢ) = tx ‼ⁱ i
      in
        Tᵢ♯ at oᵢ ∈′ UTXO txs

    -- (2)
    inputsRedeemable : ∀ (i : Fin i) →
      let
        (_ at oᵢ) = tx ‼ⁱ i
        (((_ , o , Tᵢ) at tᵢ) , _) = singleMatch i
        oᵢ = fromℕ≤ {m = oᵢ} {n = o} (noOutOfBounds i)
        vᵢ = value (proj₂ (Tᵢ ‼ᵒ oᵢ))
      in
        Tᵢ , oᵢ , tᵢ ↝[ vᵢ ] tx , i , t

    -- (3)
    valuesPreserved :
      let
        ins  = tabulate λ i → let (_ at oᵢ) = tx ‼ⁱ i
                                  (((_ , o , Tᵢ) at tᵢ) , _) = singleMatch i
                                  oᵢ = fromℕ≤ {m = oᵢ} {n = o} (noOutOfBounds i)
                              in  value (proj₂ (Tᵢ ‼ᵒ oᵢ))
        outs = V.map (value ∘ proj₂) (outputs tx)
      in
        sum ins ≥ sum outs

    -- (4)
    laterTime :
      t ≥ latestTime txs

-- Consistency.
data ConsistentBlockchain : Blockchain → Set where
  ∙_∶-_  : (tx : Tx 0 o)
         → Coinbase tx
         → ConsistentBlockchain [ (_ , _ , tx) at 0 ]

  _⊕_∶-_ : ConsistentBlockchain txs
         → (tx : Tx i o)
         → txs ▷ tx , t
         → ConsistentBlockchain (((_ , _ , tx) at t) ∷ txs)
