---------------------------------
-- Dummy-hashing Tx datatypes.
---------------------------------
module Bitcoin.DummyHash.Tx where

open import Data.Product using (_,_)
open import Data.Integer using (+_)
open import Data.List    using ([]; _∷_)

open import Bitcoin.Crypto using (KeyPair; sec)
open import Bitcoin.DummyHash.Base
open import Bitcoin.Script.Base
open import Bitcoin.Tx.Base

txi♯ : HashFunction TxInput
txi♯ (tx♯ at i) = merge♯ (tx♯ ∷ nat♯ i ∷ [])

script♯ : HashFunction ∃BitcoinScript
script♯ (_ , (ƛ _)) = + 666

txo♯ : HashFunction ∃TxOutput
txo♯ (_ , txo) = merge♯ (nat♯ (value txo) ∷ script♯ (_ , (validator txo)) ∷ [])

tx♯ : HashFunction ∃Tx
tx♯ (_ , _ , tx) = merge♯ ( vec♯ txi♯ (inputs tx)
                          ∷ vec♯ nat♯ (relLock tx)
                          ∷ vec♯ txo♯ (outputs tx)
                          ∷ nat♯ (absLock tx)
                          ∷ [] )

HASH : HashFunction (Tx i o)
HASH tx = tx♯ (_ , _ , tx)

SIG : KeyPair → HashFunction (Tx i o)
SIG k tx = merge♯ (sec k ∷ HASH tx ∷ [])
