------------------------------------------------------------------------
-- Blockchain and consistency.
------------------------------------------------------------------------
module Bitcoin.Consistency where

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Sets
open import Prelude.Functor
open import Prelude.ToN
open import Prelude.Ord
open import Prelude.InferenceRules
open import Prelude.FromList; open import Prelude.ToList

open import Bitcoin.Crypto
open import Bitcoin.BasicTypes
open import Bitcoin.Script
open import Bitcoin.Tx

-- Blockchain
Blockchain : Type
Blockchain = List TimedTx -- in reverse chronological order, in contrast to the paper

variable txs txs′ : Blockchain

txSet : Blockchain → Set⟨ TimedTx ⟩
txSet = fromList

match : Blockchain → HashId → Set⟨ TimedTx ⟩
match []                              _   = ∅
match ((∃tx@(_ , _ , tx) at t) ∷ txs) tx♯ =
  if tx ♯ == tx♯ then
    singleton (∃tx at t) ∪ match txs tx♯
  else
    match txs tx♯

-- UTXO: Unspent transaction outputs.
-- (0) EUTXO-like set-theoretic definition, based on txInputs instead of outputs for convenience
UTXOₜₓ : ∃Tx → Set⟨ TxInput ⟩
UTXOₜₓ (_ , o , tx) = fromList $ (tx ♯) at_ <$> upTo o

STXOₜₓ : ∃Tx → Set⟨ TxInput ⟩
STXOₜₓ (_ , _ , tx) = tx .inputs ∙toList ∙fromList

UTXO : Blockchain → Set⟨ TxInput ⟩
UTXO = λ where
  []              → ∅
  (tx at _ ∷ txs) → UTXO txs ─ STXOₜₓ tx
                  ∪ UTXOₜₓ tx

-- Consistent update.
latestTime : Blockchain → Time
latestTime = λ where
  []             → 0
  ((_ at t) ∷ _) → t

record _▷_,_ (txs : Blockchain) (tx : Tx i o) (t : Time) : Type where
  field
    -- well-formedness conditions

    inputsUnique :
      Unique $ tx .inputs ∙toList

    singleMatch : ∀ (j : Fin i) →
      let
        (tx♯ at _) = tx ‼ⁱ j
      in
        ∃[ tx ] (match txs tx♯ ≡ singleton tx)

    noOutOfBounds : ∀ (j : Fin i) →
      let
        (_ at oⱼ)                = tx ‼ⁱ j
        (((_ , o , _) at _) , _) = singleMatch j
      in
        oⱼ < o

  private
    getI : ∀ (j : Fin i) → let i′ , o′ , _ = singleMatch j .proj₁ .transaction in
      Tx i′ o′ × Fin o′ × Time × Value
    getI j =
      let
        (_ at oⱼ) = tx ‼ⁱ j
        (((_ , o , Tⱼ) at tⱼ) , _) = singleMatch j
        oⱼ = F.fromℕ< {m = oⱼ} {n = o} (noOutOfBounds j)
        vⱼ = (Tⱼ ‼ᵒ oⱼ) ∙value
      in
        Tⱼ , oⱼ , tⱼ , vⱼ

  field
    -- (1)
    inputs∈UTXO : ∀ (j : Fin i) →
      tx ‼ⁱ j ∈ˢ UTXO txs

    -- (2)
    inputsRedeemable : ∀ (j : Fin i) → let Tⱼ , oⱼ , tⱼ , vⱼ = getI j in
        Tⱼ , oⱼ , tⱼ ↝[ vⱼ ] tx , j , t

    -- (3)
    valuesPreserved :
      let
        ins  = V.tabulate λ j → let Tⱼ , oⱼ , _ = getI j in (Tⱼ ‼ᵒ oⱼ) ∙value
        outs = _∙value <$> tx .outputs
      in
        V.sum ins ≥ V.sum outs

    -- (4)
    laterTime :
      t ≥ latestTime txs

-- Consistency.
data ConsistentBlockchain : Blockchain → Type where
  -- ∎_∶-_  : (tx : Tx 0 o)
  --        → Coinbase tx
  --        → ConsistentBlockchain [ (_ , _ , tx) at 0 ]
  ∎  : ConsistentBlockchain []

  _⊕_∶-_ : ConsistentBlockchain txs
         → (tx : Tx i o)
         → txs ▷ tx , t
         → ConsistentBlockchain (((-, -, tx) at t) ∷ txs)

-- (1) Non-constructive/indirect formulation of the UTXO set, via describing when an output is unspent.
Unspent : (b : Blockchain) → (i : Index b) → let (_ , o , Tⱼ) at tⱼ = b ‼ i in
        ∀ (j : Fin o) → Type
Unspent b i j =
  let (_ , o , Tⱼ) at tⱼ = b ‼ i in
  ∀ (i′ : Index b) (leq : i′ F.≤ i)  → let (i′ , _ , Tⱼ′) at tⱼ′ = b ‼ i′ in
  ∀ (j′ : Fin i′) →
    Tⱼ , j , tⱼ ↛ Tⱼ′ , j′ , tⱼ′

Unspent-∷ : ∀ {tx t} {b : Blockchain} {i : Index b} → let (_ , o , Tⱼ) at tⱼ = b ‼ i in ∀ {j : Fin o} →
  ∙ Unspent b i j
  ∙ (((Tⱼ ♯at j) V.Mem.∉ ∃inputs tx)
    ─────────────────────────────────────────────────────────
    Unspent ((tx at t) ∷ b) (fsuc i) j)
Unspent-∷ {tx = tx} unsp in∉ 0F 0≤ j′ (v , record {input~output = io})
  = in∉ (subst (V.Mem._∈ ∃inputs tx) io (V.Mem.∈-lookup j′ _))
Unspent-∷ unsp _ (fsuc i′) (s≤s leq) j′ p
  = unsp i′ leq j′ p

--

∃Unspent : (b : Blockchain) → ∃TxOutput → Type
∃Unspent b txo =
  Σ (Index b) λ i →
    let (_ , o , Tⱼ) at _ = b ‼ i in
    Σ (Fin o) λ j →
      Unspent b i j × (Tⱼ ‼ᵒ j ≡ txo)

↝-irreflexive : ∀ {T : Tx i o} {oⱼ : Fin o} {iⱼ : Fin i} {t₀ t v t′}
  → ConsistentBlockchain [ (-, -, T) at t₀ ]
  → ¬ (T , oⱼ , t ↝[ v ] T , iⱼ , t′)
↝-irreflexive {T = T} {iⱼ = iⱼ} (∙ ⊕ .T ∶- record {inputs∈UTXO = i∈}) _ = ⊥-elim $ ∉∅ _ (i∈ iⱼ)

--

∃Unspent-∷ : ∀ {t tx b o} →
  ∙ ConsistentBlockchain ((tx at t) ∷ b)
  → (wit : ∃Unspent b o)
  → let i , j , _ = wit; (_ , _ , Tⱼ) at _ = b ‼ i in
  ∙ (Tⱼ ♯at j V.Mem.∉ ∃inputs tx)
    ─────────────────────────────────────────────────────────
    ∃Unspent ((tx at t) ∷ b) o
∃Unspent-∷ vb (i , j , p , o≡) in∉ = fsuc i , j , Unspent-∷ p in∉ , o≡

-- (2) Alternative set-theoretic/constructive formulation of the UTXO set, similar to the one in EUTXO.
stxo : ∀ {tx b t} → ConsistentBlockchain ((tx at t) ∷ b) → List ∃TxOutput
stxo {tx = i , _ , _} (_ ⊕ tx ∶- p)
  = map f (allFin i)
  module ∣stxo∣ where
    f : Fin i → ∃TxOutput
    f j =
      let
        record {singleMatch = singleMatch; noOutOfBounds = noOutOfBounds} = p
        (_ at oⱼ) = tx ‼ⁱ j
        (((_ , o , Tⱼ) at tⱼ) , _) = singleMatch j
        oⱼ = F.fromℕ< {m = oⱼ} {n = o} (noOutOfBounds j)
      in
        Tⱼ ‼ᵒ oⱼ

utxoₜₓ : ∃Tx → Set⟨ ∃TxOutput ⟩
utxoₜₓ (_ , _ , tx) = tx .outputs ∙toList ∙fromList

utxo : (b : Blockchain) → ConsistentBlockchain b → Set⟨ ∃TxOutput ⟩
utxo .[] ∎ = ∅
utxo (.((_ , _ , tx) at _) ∷ b) vb₀@(vb ⊕ tx ∶- _)
  = utxo b vb ─ fromList (stxo vb₀)
  ∪ utxoₜₓ (-, -, tx)

-- T0D0: prove equivalence between (1) and (2)

-- Unspent : (b : Blockchain) → (i : Index b) → let (_ , o , Tⱼ) at tⱼ = b ‼ i in ∀ (j : Fin o) → Type
-- utxo : (b : Blockchain) → ConsistentBlockchain b → Set⟨ ∃TxOutput ⟩
-- UTXO : Blockchain → Set⟨ TxInput ⟩

{-
Unspent→UTXO : ∀ {b : Blockchain} {i : Index b} → let _ , o , tx = transaction (b ‼ i) in
               ∀ {j : Fin o}
  → Unspent b i j
    ─────────────────────────────────────────────────────────
    ((tx ♯) at toℕ j) ∈ˢ UTXO b
Unspent→UTXO {b} {i} {j} p = {!!}

UTXO→Unspent : ∀ {b : Blockchain} {i : Index b} → let _ , o , tx = transaction (b ‼ i) in
               ∀ {j : Fin o}
  → ((tx ♯) at toℕ j) ∈ˢ UTXO b
    ─────────────────────────────────────────────────────────
    Unspent b i j
UTXO→Unspent {x ∷ b} {i} {j} p = {!!}
-}

{- WIP
-- record BlockchainTx : Type where
--   field
--     b : Blockchain
--     i : Index b

--   getTTx : TimedTx
--   getTTx = b ‼ i

--   getTx : ∃Tx
--   getTx = transaction (getTTx b)

-- BlockchainTx = Σ[ b ∈ Blockchain ] Index b

-- getTTx : BlockchainTx → TimedTx
-- getTTx (b , i) = b ‼ i

-- getTx : BlockchainTx → ∃Tx
-- getTx = transaction ∘ getTTx

-- Unspent : (btx : BlockchainTx) →  Pred₀ (Fin $ ∃o $ getTx btx)
-- Unspent (b , i) j =
--   let (_ , o , Tⱼ) at tⱼ = b ‼ i in
--   ∀ (i′ : Index b) (leq : i′ F.≤ i) → let (i′ , _ , Tⱼ′) at tⱼ′ = b ‼ i′ in
--   ∀ (j′ : Fin i′) →
--     Tⱼ , j , tⱼ ↛ Tⱼ′ , j′ , tⱼ′
-}
