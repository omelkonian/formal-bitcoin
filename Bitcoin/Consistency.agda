------------------------------------------------------------------------
-- Blockchain and consistency.
------------------------------------------------------------------------
module Bitcoin.Consistency where

open import Data.Fin  using (fromℕ<)

open import Prelude.Init
open import Prelude.General
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Sets
open import Prelude.Functor

open import Bitcoin.Crypto
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
match ((tx at t) ∷ txs) tx♯ with tx ♯ ≟ tx♯
... | no _  = match txs tx♯
... | yes _ = singleton (tx at t)
            ∪ match txs tx♯

-- UTXO: Unspent transaction outputs.
UTXOₜₓ : ∃Tx → Set⟨ TxInput ⟩
UTXOₜₓ ∃tx@(_ , o , tx) = fromList $ map (λ i → (∃tx ♯) at i) (upTo o)

STXOₜₓ : ∃Tx → Set⟨ TxInput ⟩
STXOₜₓ (_ , _ , tx) = fromList (V.toList $ inputs tx)

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
      tx ‼ⁱ i ∈ˢ UTXO txs

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
  -- ∙_∶-_  : (tx : Tx 0 o)
  --        → Coinbase tx
  --        → ConsistentBlockchain [ (_ , _ , tx) at 0 ]
  ∙  : ConsistentBlockchain []

  _⊕_∶-_ : ConsistentBlockchain txs
         → (tx : Tx i o)
         → txs ▷ tx , t
         → ConsistentBlockchain (((_ , _ , tx) at t) ∷ txs)

stxo : ∀ {tx b t} → ConsistentBlockchain ((tx at t) ∷ b) → List ∃TxOutput
stxo {tx = i , _ , .tx} (_ ⊕ tx ∶- p)
  = map f (allFin i)
  module ∣stxo∣ where
    f : Fin i → ∃TxOutput
    f i =
      let
        record {singleMatch = singleMatch; noOutOfBounds = noOutOfBounds} = p
        (_ at oᵢ) = tx ‼ⁱ i
        (((_ , o , Tᵢ) at tᵢ) , _) = singleMatch i
        oᵢ = fromℕ< {m = oᵢ} {n = o} (noOutOfBounds i)
      in
        Tᵢ ‼ᵒ oᵢ

utxoₜₓ : ∃Tx → Set⟨ ∃TxOutput ⟩
utxoₜₓ (_ , _ , tx) = fromList (V.toList $ outputs tx)

utxo : (b : Blockchain) → ConsistentBlockchain b → Set⟨ ∃TxOutput ⟩
utxo .[] ∙ = ∅
utxo (.((_ , _ , tx) at _) ∷ b) vb₀@(vb ⊕ tx ∶- _)
  = utxo b vb ─ fromList (stxo vb₀)
  ∪ utxoₜₓ (-, -, tx)

Unspent : (b : Blockchain) → (i : Index b) → let (_ , o , Tᵢ) at tᵢ = b ‼ i in
        ∀ (j : Fin o) → Set
Unspent b i j =
  let (_ , o , Tᵢ) at tᵢ = b ‼ i in
  ∀ (i′ : Index b) (leq : i′ F.≤ i)  → let (i′ , _ , Tᵢ′) at tᵢ′ = b ‼ i′ in
  ∀ (j′ : Fin i′) →
    Tᵢ , j , tᵢ ↛ Tᵢ′ , j′ , tᵢ′

Unspent-∷ : ∀ {tx t} {b : Blockchain} {i : Index b} → let (_ , o , Tᵢ) at tᵢ = b ‼ i in ∀ {j : Fin o}
  → Unspent b i j
  → ((Tᵢ atᵒ j) V.Mem.∉ ∃inputs tx)
    ----------------------------------
  → Unspent ((tx at t) ∷ b) (fsuc i) j
Unspent-∷ {tx = tx} unsp in∉ 0F 0≤ j′ (v , record {input~output = io})
  = in∉ (subst (V.Mem._∈ ∃inputs tx) io (V.Mem.∈-lookup j′ _))
Unspent-∷ unsp _ (fsuc i′) (s≤s leq) j′ p
  = unsp i′ leq j′ p

--

∃Unspent : (b : Blockchain) → ∃TxOutput → Set
∃Unspent b txo =
  Σ (Index b) λ i →
    let (_ , o , Tᵢ) at _ = b ‼ i in
    Σ (Fin o) λ j →
      Unspent b i j × (Tᵢ ‼ᵒ j ≡ txo)



↝-irreflexive : ∀ {T : Tx i o} {oᵢ : Fin o} {iᵢ : Fin i} {t₀ t v t′}
  → ConsistentBlockchain [ (-, -, T) at t₀ ]
  → ¬ (T , oᵢ , t ↝[ v ] T , iᵢ , t′)
↝-irreflexive {T = T} {iᵢ = iᵢ} (∙ ⊕ .T ∶- record {inputs∈UTXO = i∈}) _ = ⊥-elim $ ∉∅ _ (i∈ iᵢ)

--

∃Unspent-∷ : ∀ {t tx b o}
  → (vb : ConsistentBlockchain $ (tx at t) ∷ b)
  → (wit : ∃Unspent b o) → let i , j , _ = wit; (_ , _ , Tᵢ) at _ = b ‼ i in
    (Tᵢ atᵒ j V.Mem.∉ ∃inputs tx)
    --------------------------
  → ∃Unspent ((tx at t) ∷ b) o
∃Unspent-∷ vb (i , j , p , o≡) in∉ = fsuc i , j , Unspent-∷ p in∉ , o≡
