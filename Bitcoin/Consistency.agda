------------------------------------------------------------------------
-- Blockchain and consistency.
------------------------------------------------------------------------
module Bitcoin.Consistency where

open import Data.Fin  using (fromℕ<)

open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Set'

open import Bitcoin.BasicTypes
open import Bitcoin.Script.Base
open import Bitcoin.Tx.Base
open import Bitcoin.Tx.Crypto
open import Bitcoin.Tx.Semantics

-- Blockchain
Blockchain : Set
Blockchain = List TimedTx -- in reverse chronological order, in contrast to the paper

variable txs txs′ : Blockchain

txSet : Blockchain → Set⟨ TimedTx ⟩
txSet = fromList

match : Blockchain → HashId → Set⟨ TimedTx ⟩
match []                _   = ∅
match ((tx at t) ∷ txs) tx′ with hashTx tx ≟ tx′
... | no _  = match txs tx′
... | yes _ = singleton (tx at t)
            ∪ match txs tx′

-- UTXO: Unspent transaction outputs.
UTXOₜₓ : ∃Tx → Set⟨ TxInput ⟩
UTXOₜₓ ∃tx@(_ , o , tx) = fromList (map (λ i → hashTx ∃tx at i) (upTo o))

STXOₜₓ : ∃Tx → Set⟨ TxInput ⟩
STXOₜₓ (_ , _ , tx) = fromList (V.toList (inputs tx))

UTXO : Blockchain → Set⟨ TxInput ⟩
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
      Unique (V.toList (inputs tx))

    singleMatch : ∀ (i : Fin i) →
      let
        (tx♯ at _) = tx ‼ⁱ i
      in
        ∃[ tx ] (match txs tx♯ ≡ singleton tx)

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
        oᵢ = fromℕ< {m = oᵢ} {n = o} (noOutOfBounds i)
        vᵢ = value (proj₂ (Tᵢ ‼ᵒ oᵢ))
      in
        Tᵢ , oᵢ , tᵢ ↝[ vᵢ ] tx , i , t

    -- (3)
    valuesPreserved :
      let
        ins  = V.tabulate λ i → let (_ at oᵢ) = tx ‼ⁱ i
                                    (((_ , o , Tᵢ) at tᵢ) , _) = singleMatch i
                                    oᵢ = fromℕ< {m = oᵢ} {n = o} (noOutOfBounds i)
                                in value (proj₂ (Tᵢ ‼ᵒ oᵢ))
        outs = V.map (value ∘ proj₂) (outputs tx)
      in
        V.sum ins ≥ V.sum outs

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
