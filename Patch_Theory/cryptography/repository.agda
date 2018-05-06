{-# OPTIONS --type-in-type #-}

open import Function renaming (_∘_ to _○_)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Reflection
open import Data.List
open import Patch_Theory.agda_lib.Utils

open import Patch_Theory.cryptography.Paillier-Cryptosystem
open import Patch_Theory.cryptography.RSA-Cryptosystem
open import Patch_Theory.cryptography.OPE-Cryptosystem
open import Patch_Theory.cryptography.ElGamal-Cryptosystem
open import Patch_Theory.cryptography.insert-delete-query
open import Patch_Theory.cryptography.increment-path
open import Patch_Theory.cryptography.encrypted-increment

open import Automation.generateRec
open import Automation.generateInd
open import Automation.generateHit
open import Automation.generateRecHit
open import Automation.generateIndHit
open import Automation.reflectionUtils
open import Automation.pathUtils


module Patch_Theory.cryptography.repository where

module History_hit where

{-- Records : Higher inductive type which stores the instances of all the queries executed --}

  private
    data #History : Nat → Nat → Set where
      #[]R : {m : Nat} → #History m m
      #ID-R:: : {m n : Nat} → #History m n → #History m n
      #INSERT_at_::_ : {m n : Nat} → (value : Int) → (i : Nat) → #History m n → #History m (suc n)
      #DELETE_::_ : {m n : Nat} → (i : Nat) → #History m (suc n) → #History m n
      #RSA-ENCRYPT_,_::_ : {m n : Nat} → (p : Nat) → (q : Nat) → #History m n → #History m n
      #RSA-DECRYPT_,_::_ : {m n : Nat} → (p : Nat) → (q : Nat) → #History m n → #History m n
      #PAILLIER-ENCRYPT_,_::_ : {m n : Nat} → (p : Nat) → (q : Nat) → #History m n → #History m n
      #PAILLIER-DECRYPT_,_::_ : {m n : Nat} → (p : Nat) → (q : Nat) → #History m n → #History m n
      #OPE-ENCRYPT::_ : {m n : Nat} → #History m n → #History m n
      #OPE-DECRYPT::_ : {m n : Nat} → #History m n → #History m n
      #ELGAMAL-ENCRYPT_::_ : {m n : Nat} → (p : Nat) → #History m n → #History m n
      #ELGAMAL-DECRYPT_::_ : {m n : Nat} → (p : Nat) → #History m n → #History m n
      #INCREMENT100_::_ : {m n : Nat} → (i : Nat) → #History m n → #History m n
      #CRYPT-INCREMENT100_,_,_::_ : {m n : Nat} → (p q : Nat) → (i : Nat) → #History m n → #History m n


  unquoteDecl History Recpoints []R ID-R:: INSERT_at_::_ DELETE_::_ RSA-ENCRYPT_,_::_ RSA-DECRYPT_,_::_ PAILLIER-ENCRYPT_,_::_ PAILLIER-DECRYPT_,_::_
                                OPE-ENCRYPT::_ OPE-DECRYPT::_ ELGAMAL-ENCRYPT_::_ ELGAMAL-DECRYPT_::_ INCREMENT100_::_ CRYPT-INCREMENT100_,_,_::_
                      Recpaths PAILLIER-HOMOMORPHISM_,_,_::_ = data-hit (quote #History) History
                                                                    Recpoints ([]R ∷ ID-R:: ∷ INSERT_at_::_ ∷ DELETE_::_ ∷ RSA-ENCRYPT_,_::_ ∷ RSA-DECRYPT_,_::_ ∷
                                                                               PAILLIER-ENCRYPT_,_::_ ∷ PAILLIER-DECRYPT_,_::_ ∷ OPE-ENCRYPT::_ ∷ OPE-DECRYPT::_ ∷ ELGAMAL-ENCRYPT_::_ ∷
                                                                               ELGAMAL-DECRYPT_::_ ∷ INCREMENT100_::_ ∷ CRYPT-INCREMENT100_,_,_::_ ∷ []) -- point constructors
                                                                    Recpaths (PAILLIER-HOMOMORPHISM_,_,_::_ ∷ []) -- path constructors
                                                                    (argPath ({m n : Nat} → (p q : Nat) → (i : Nat) → (r : #History m n) →
                                                                             (#PAILLIER-DECRYPT_,_::_ {m} {n} p q (#CRYPT-INCREMENT100_,_,_::_ {m} {n} p q i
                                                                             (#PAILLIER-ENCRYPT_,_::_ {m} {n} p q r))) ≡ (#INCREMENT100_::_  {m} {n} i r)) ∷ [])
                                                                    --  argPath ({m n : Nat} → (p q : Nat) → (r : #History m n) →
                                                                       --       (#PAILLIER-DECRYPT_,_::_ p q (#PAILLIER-ENCRYPT_,_::_ p q r)) ≡ (#ID-R:: r)) ∷ [])


  unquoteDecl recHistory* = generateRec (vArg recHistory*)
                                        (quote #History) (1 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ [])


  unquoteDecl recHistory βrecHistory-paiHom = generateRecHit (vArg recHistory) ((vArg βrecHistory-paiHom) ∷ [])
                                                             (quote #History) (1 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ [])
                                                             (quote recHistory*)
                                                             (quote History) Recpoints Recpaths

  unquoteDecl indHistory* = generateInd (vArg indHistory*)
                                        (quote #History) (1 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ [])

  unquoteDecl indHistory βindHistory-paiHom = generateIndHit (vArg indHistory) ((vArg βindHistory-paiHom) ∷ [])
                                                             (quote #History) (1 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ 2 ∷ [])
                                                             (quote indHistory*)
                                                             (quote History) Recpoints Recpaths


  postulate
    paillier-rec-hom : (p q : Nat) → (i : Nat) → (vec : List Int) → (paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q)) vec ≡
                                                                     (increment-100 i) vec


  {-# TERMINATING #-}
  replay' : {m n : Nat} → History m n → List Int
  replay' {m} {n} r = recHistory* r (List Int) [] (λ r ls → id (replay' r))
                                              (λ val i r ls → insert val i (replay' r))
                                              (λ i r ls → delete i (replay' r))
                                              (λ p q r ls → rsa-encrypt p q (replay' r))
                                              (λ p q r ls → rsa-decrypt p q (replay' r))
                                              (λ p q r ls → paillier-encrypt p q (replay' r))
                                              (λ p q r ls → paillier-decrypt p q (replay' r))
                                              (λ r ls → ope-encrypt (replay' r))
                                              (λ r ls → ope-decrypt (replay' r))
                                              (λ p r ls → ElGamal-encrypt2 p (ElGamal-encrypt p (replay' r)))
                                              (λ p r ls → ElGamal-decrypt p (ElGamal-decrypt2 p (replay' r)))
                                              (λ i r ls → increment-100 i (replay' r))
                                              (λ p q i r ls → crypt-increment-100 p q i (replay' r))

  replay : {n : Nat} → History 0 n → List Int
  replay {n} r = replay' {0} {n} r

  postulate
    paillier-rec-hom' : {m n : Nat} → (p q : Nat) → (i : Nat) → (r : History m n) → (paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q)) (replay' r) ≡
                                                                                     (increment-100 i) (replay' r)


  replayP' : {m n : Nat} → History m n → List Int
  replayP' {m} {n} r = recHistory r (List Int) [] (λ r ls → id (replay' r))
                                              (λ val i r ls → insert val i (replay' r))
                                              (λ i r ls → delete i (replay' r))
                                              (λ p q r ls → rsa-encrypt p q (replay' r))
                                              (λ p q r ls → rsa-decrypt p q (replay' r))
                                              (λ p q r ls → paillier-encrypt p q (replay' r))
                                              (λ p q r ls → paillier-decrypt p q (replay' r))
                                              (λ r ls → ope-encrypt (replay' r))
                                              (λ r ls → ope-decrypt (replay' r))
                                              (λ p r ls → ElGamal-encrypt2 p (ElGamal-encrypt p (replay' r)))
                                              (λ p r ls → ElGamal-decrypt p (ElGamal-decrypt2 p (replay' r)))
                                              (λ i r ls → increment-100 i (replay' r))
                                              (λ p q i r ls → crypt-increment-100 p q i (replay' r))
                                              (λ p q i r → (paillier-rec-hom' p q i r))

  replayP : {n : Nat} → History 0 n → List Int
  replayP {n} r = replayP' {0} {n} r


  {-- I-history-paiHom-path : Interprets the insert-query path in cryptR as a path in the Universe given by insert function --}
  I-history-paiHom-path : {n : Nat} → (p q : Nat) → (i : Nat) → (r : History 0 n) →
                         ap replay (PAILLIER-HOMOMORPHISM_,_,_::_ p q i r) ≡ (paillier-rec-hom p q i (replay r))
  I-history-paiHom-path {n} p q i r = βrecHistory-paiHom (List Int) [] (λ r ls → id (replay' r))
                                              (λ val i r ls → insert val i (replay' r))
                                              (λ i r ls → delete i (replay' r))
                                              (λ p q r ls → rsa-encrypt p q (replay' r))
                                              (λ p q r ls → rsa-decrypt p q (replay' r))
                                              (λ p q r ls → paillier-encrypt p q (replay' r))
                                              (λ p q r ls → paillier-decrypt p q (replay' r))
                                              (λ r ls → ope-encrypt (replay' r))
                                              (λ r ls → ope-decrypt (replay' r))
                                              (λ p r ls → ElGamal-encrypt2 p (ElGamal-encrypt p (replay' r)))
                                              (λ p r ls → ElGamal-decrypt p (ElGamal-decrypt2 p (replay' r)))
                                              (λ i r ls → increment-100 i (replay' r))
                                              (λ p q i r ls → crypt-increment-100 p q i (replay' r))
                                              (λ p q i r → (paillier-rec-hom p q i (replay' r)))



open History_hit public

module Document_hit where

{-- cryptR : Higher inductive type representing the database tables as points and encryption, decryption functions and queries as paths --}

  private
    data #cryptR : Set where
      #ctab_ : {n : Nat} → History 0 n → #cryptR
      #ctabRSA_ : {n : Nat} → History 0 n → #cryptR
      #ctabPL_ : {n : Nat} → History 0 n → #cryptR
      #ctabOPE_ : {n : Nat} → History 0 n → #cryptR
      #ctabEG_ : {n : Nat} → History 0 n → #cryptR
                    
  unquoteDecl cryptR cryptRpoints ctab_ ctabRSA_ ctabPL_ ctabOPE_ ctabEG_
                     cryptRpaths insert-query delete-query rsa-enc rsa-dec
                                 paillier-enc paillier-dec ope-enc ope-dec
                                 elgamalrsa-enc elgamalrsa-dec elgamalope-enc elgamalope-dec 
                                 increment-by-100 crypt-increment-by-100 id-cryptR = data-hit (quote #cryptR) cryptR
                                                                    cryptRpoints (ctab_ ∷ ctabRSA_ ∷ ctabPL_ ∷ ctabOPE_ ∷ ctabEG_ ∷ []) -- point constructors
                                                                    cryptRpaths (insert-query ∷ delete-query ∷ rsa-enc ∷ rsa-dec ∷ paillier-enc ∷ paillier-dec ∷ ope-enc ∷ ope-dec ∷
                                                                                 elgamalrsa-enc ∷ elgamalrsa-dec ∷ elgamalope-enc ∷ elgamalope-dec ∷ increment-by-100 ∷ crypt-increment-by-100 ∷
                                                                                 id-cryptR ∷ []) -- path constructors
                                                                    (argPath ({n : Nat} → (value : Int) → (i : Nat) → (r : History 0 n) → (#ctab r) ≡ (#ctab (INSERT value at i :: r))) ∷
                                                                     argPath ({n : Nat} → (i : Nat) → (r : History 0 (suc n)) → (#ctab r) ≡ (#ctab (DELETE i :: r))) ∷
                                                                     argPath ({n : Nat} → (p : Nat) → (q : Nat) → (r : History 0 n) → (#ctab r) ≡ (#ctabRSA (RSA-ENCRYPT p , q :: r))) ∷
                                                                     argPath ({n : Nat} → (p : Nat) → (q : Nat) → (r : History 0 n) → (#ctabRSA r) ≡ (#ctab (RSA-DECRYPT p , q :: r))) ∷
                                                                     argPath ({n : Nat} → (p : Nat) → (q : Nat) → (r : History 0 n) → (#ctab r) ≡ (#ctabPL (PAILLIER-ENCRYPT p , q :: r))) ∷
                                                                     argPath ({n : Nat} → (p : Nat) → (q : Nat) → (r : History 0 n) → (#ctabPL r) ≡ (#ctab (PAILLIER-DECRYPT p , q :: r))) ∷
                                                                     argPath ({n : Nat} → (r : History 0 n) → (#ctab r) ≡ (#ctabOPE (OPE-ENCRYPT:: r))) ∷
                                                                     argPath ({n : Nat} → (r : History 0 n) → (#ctabPL r) ≡ (#ctab (OPE-DECRYPT:: r))) ∷
                                                                     argPath ({n : Nat} → (p : Nat) → (r : History 0 n) → (#ctabRSA r) ≡ (#ctabEG (ELGAMAL-ENCRYPT p :: r))) ∷
                                                                     argPath ({n : Nat} → (p : Nat) → (r : History 0 n) → (#ctabEG r) ≡ (#ctabRSA (ELGAMAL-DECRYPT p :: r))) ∷
                                                                     argPath ({n : Nat} → (p : Nat) → (r : History 0 n) → (#ctabOPE r) ≡ (#ctabEG (ELGAMAL-ENCRYPT p :: r))) ∷
                                                                     argPath ({n : Nat} → (p : Nat) → (r : History 0 n) → (#ctabEG r) ≡ (#ctabOPE (ELGAMAL-DECRYPT p :: r))) ∷
                                                                     argPath ({n : Nat} → (i : Nat) → (r : History 0 n) → (#ctab r) ≡ (#ctab (INCREMENT100 i :: r))) ∷
                                                                     argPath ({n : Nat} → (p q : Nat) → (i : Nat) → (r : History 0 n) → (#ctabPL r) ≡ (#ctabPL (CRYPT-INCREMENT100 p , q , i :: r))) ∷
                                                                     argPath ({n : Nat} → (r : History 0 n) → (#ctab r) ≡ (#ctab (ID-R:: r))) ∷ [])

  unquoteDecl reccryptR* = generateRec (vArg reccryptR*)
                                       (quote #cryptR) (0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ [])


  unquoteDecl reccryptR βreccryptR-insertQ βreccryptR-deleteQ βreccryptR-rsaE βreccryptR-rsaD βreccryptR-paillierE βreccryptR-paillierD
              βreccryptR-OPEE βreccryptR-OPED βreccryptR-ElgRSAE βreccryptR-ElgRSAD βreccryptR-ElgOPEE βreccryptR-ElgOPED
              βreccryptR-increment100 βreccryptR-crypt-inc βreccryptR-id
              = generateRecHit (vArg reccryptR)
                               ((vArg βreccryptR-insertQ) ∷ (vArg βreccryptR-deleteQ) ∷ (vArg βreccryptR-rsaE) ∷ (vArg βreccryptR-rsaD) ∷
                                (vArg βreccryptR-paillierE) ∷ (vArg βreccryptR-paillierD) ∷ (vArg βreccryptR-OPEE) ∷ (vArg βreccryptR-OPED) ∷
                                (vArg βreccryptR-ElgRSAE) ∷ (vArg βreccryptR-ElgRSAD) ∷ (vArg βreccryptR-ElgOPEE) ∷ (vArg βreccryptR-ElgOPED) ∷
                                (vArg βreccryptR-increment100) ∷ (vArg βreccryptR-crypt-inc) ∷ (vArg βreccryptR-id) ∷ [])
                               (quote #cryptR) (0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ [])
                               (quote reccryptR*)
                               (quote cryptR) cryptRpoints cryptRpaths

  unquoteDecl indcryptR* = generateInd (vArg indcryptR*)
                                       (quote #cryptR) (0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ [])

  unquoteDecl indcryptR βindcryptR-insertQ βindcryptR-deleteQ βindcryptR-rsaE βindcryptR-rsaD βindcryptR-paillierE βindcryptR-paillierD
              βindcryptR-OPEE βindcryptR-OPED βindcryptR-ElgRSAE βindcryptR-ElgRSAD βindcryptR-ElgOPEE βindcryptR-ElgOPED
              βindcryptR-increment100 βindcryptR-crypt-inc βindcryptR-id
              = generateIndHit (vArg indcryptR)
                               ((vArg βindcryptR-insertQ) ∷ (vArg βindcryptR-deleteQ) ∷ (vArg βindcryptR-rsaE) ∷ (vArg βindcryptR-rsaD) ∷
                                (vArg βindcryptR-paillierE) ∷ (vArg βindcryptR-paillierD) ∷ (vArg βindcryptR-OPEE) ∷ (vArg βindcryptR-OPED) ∷
                                (vArg βindcryptR-ElgRSAE) ∷ (vArg βindcryptR-ElgRSAD) ∷ (vArg βindcryptR-ElgOPEE) ∷ (vArg βindcryptR-ElgOPED) ∷
                                (vArg βindcryptR-increment100) ∷ (vArg βindcryptR-crypt-inc) ∷ (vArg βindcryptR-id) ∷ [])
                               (quote #cryptR) (0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ [])
                               (quote indcryptR*)
                               (quote cryptR) cryptRpoints cryptRpaths


  paillier-homRToC : {n : Nat} → (p q : Nat) → (i : Nat) → (r : History 0 n) → (ctab  (PAILLIER-DECRYPT p , q :: (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))))
                                                                                   ≡ (ctab (INCREMENT100 i :: r))
  paillier-homRToC p q i r = ! ((paillier-enc p q r) ∘ (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r)))) ∘ (increment-by-100 i r)

  postulate
    paillier-homRecToCDB : {n : Nat} → (p q : Nat) → (i : Nat) → (r : History 0 n) →
                           ap ctab_ (PAILLIER-HOMOMORPHISM_,_,_::_ p q i r) ≡ paillier-homRToC p q i r


  I-cryptR : cryptR → Set
  I-cryptR r = reccryptR r Set (λ x → (Singleton (replay x)))
                                 (λ x → (Singleton (replay x)))
                                 (λ x → (Singleton (replay x)))
                                 (λ x → (Singleton (replay x)))
                                 (λ x → (Singleton (replay x)))
                                 (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                 (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                 (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                 (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                 (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                 (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                 (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                 (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                 (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                  (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                 (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                      (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                 (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                  (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                 (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                      (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                 (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                 (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                 (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

open Document_hit public


{-- I-cryptR-insert-path : Interprets the insert-query path in cryptR as a path in the Universe given by insert function --}
I-cryptR-insert-path : {n : Nat} → (value : Int) → (i : Nat) → (r : History 0 n) →
                       ap I-cryptR (insert-query value i r) ≡ ua (singleton-equiv {List Int} {List Int} {(insert value i)} (to-Singleton (insert value i)))
I-cryptR-insert-path value i r = βreccryptR-insertQ Set (λ x → (Singleton (replay x)))
                                                         (λ x → (Singleton (replay x)))
                                                         (λ x → (Singleton (replay x)))
                                                         (λ x → (Singleton (replay x)))
                                                         (λ x → (Singleton (replay x)))
                                                         (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                                         (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                                         (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                                         (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                                         (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                                         (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                                         (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                                         (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                                         (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                       (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                         (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                       (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                         (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                       (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                         (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                       (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                         (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                                         (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                                         (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))
                                                         
{-- I-cryptR-delete-path : Interprets the delete-query path in cryptR as a path in the Universe given by delete function --}
I-cryptR-delete-path : {n : Nat} → (i : Nat) → (r : History 0 (suc n)) →
                       ap I-cryptR (delete-query i r) ≡ ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i)))
I-cryptR-delete-path i r = βreccryptR-deleteQ Set (λ x → (Singleton (replay x)))
                                                   (λ x → (Singleton (replay x)))
                                                   (λ x → (Singleton (replay x)))
                                                   (λ x → (Singleton (replay x)))
                                                   (λ x → (Singleton (replay x)))
                                                   (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                                   (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                                   (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                                   (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                                   (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                                   (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                                   (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                                   (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                                   (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                       (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                   (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                       (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                   (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                       (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                   (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                       (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                   (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                                   (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                                   (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-rsa-enc : Interprets the rsa-enc path in cryptR as a path in the Universe given by rsa-encrypt function --}
I-cryptR-rsa-enc : {n : Nat} → (p q : Nat) → (r : History 0 n) → ap I-cryptR (rsa-enc p q r) ≡ ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q)))
I-cryptR-rsa-enc p q r = βreccryptR-rsaE Set (λ x → (Singleton (replay x)))
                                             (λ x → (Singleton (replay x)))
                                             (λ x → (Singleton (replay x)))
                                             (λ x → (Singleton (replay x)))
                                             (λ x → (Singleton (replay x)))
                                             (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                             (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                             (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                             (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                             (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                             (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                             (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                             (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                             (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                           (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                             (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                           (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                             (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                           (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                             (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                           (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                             (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                             (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                             (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-rsa-dec : Interprets the rsa-dec path in cryptR as a path in the Universe given by rsa-decrypt function --}
I-cryptR-rsa-dec : {n : Nat} → (p q : Nat) → (r : History 0 n) →
                   ap I-cryptR (rsa-dec p q r) ≡ ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q)))
I-cryptR-rsa-dec p q r = βreccryptR-rsaD Set (λ x → (Singleton (replay x)))
                                             (λ x → (Singleton (replay x)))
                                             (λ x → (Singleton (replay x)))
                                             (λ x → (Singleton (replay x)))
                                             (λ x → (Singleton (replay x)))
                                             (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                             (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                             (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                             (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                             (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                             (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                             (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                             (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                             (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                 (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                             (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                 (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                             (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                 (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                             (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                 (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                             (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                             (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                             (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-paillier-path : Interprets the paillier-enc path in cryptR as a path in the Universe given by paillier-encrypt function --}
I-cryptR-paillier-enc : {n : Nat} → (p q : Nat) → (r : History 0 n) →
                        ap I-cryptR (paillier-enc p q r) ≡ ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q)))
I-cryptR-paillier-enc p q r = βreccryptR-paillierE Set (λ x → (Singleton (replay x)))
                                                       (λ x → (Singleton (replay x)))
                                                       (λ x → (Singleton (replay x)))
                                                       (λ x → (Singleton (replay x)))
                                                       (λ x → (Singleton (replay x)))
                                                       (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                                       (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                                       (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                                       (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                                       (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                                       (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                                       (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                                       (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                                       (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                          (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                       (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                          (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                       (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                          (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                       (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                          (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                       (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                                       (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                                       (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-paillier-path-inv : Interprets the paillier-dec path in cryptR as a path in the Universe given by paillier-decrypt function --}
I-cryptR-paillier-dec : {n : Nat} → (p q : Nat) → (r : History 0 n) →
                        ap I-cryptR (paillier-dec p q r) ≡ ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q)))
I-cryptR-paillier-dec p q r = βreccryptR-paillierD Set (λ x → (Singleton (replay x)))
                                                       (λ x → (Singleton (replay x)))
                                                       (λ x → (Singleton (replay x)))
                                                       (λ x → (Singleton (replay x)))
                                                       (λ x → (Singleton (replay x)))
                                                       (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                                       (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                                       (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                                       (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                                       (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                                       (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                                       (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                                       (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                                       (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                          (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                       (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                          (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                       (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                          (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                       (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                          (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                       (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                                       (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                                       (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-ope-enc : Interprets the ope-enc path in cryptR as a path in the Universe given by ope-encrypt function --}
I-cryptR-ope-enc : {n : Nat} → (r : History 0 n) →
                   ap I-cryptR (ope-enc r) ≡ ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt))
I-cryptR-ope-enc r = βreccryptR-OPEE Set (λ x → (Singleton (replay x)))
                                         (λ x → (Singleton (replay x)))
                                         (λ x → (Singleton (replay x)))
                                         (λ x → (Singleton (replay x)))
                                         (λ x → (Singleton (replay x)))
                                         (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                         (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                         (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                         (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                         (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                         (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                         (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                         (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                         (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                            (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                         (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                            (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                         (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                            (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                         (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                            (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                         (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                         (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                         (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-ope-dec : Interprets the ope-dec path in cryptR as a path in the Universe given by ope-decrypt function --}
I-cryptR-ope-dec : {n : Nat} → (r : History 0 n) →
                   ap I-cryptR (ope-dec r) ≡ ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt))
I-cryptR-ope-dec r = βreccryptR-OPED Set (λ x → (Singleton (replay x)))
                                         (λ x → (Singleton (replay x)))
                                         (λ x → (Singleton (replay x)))
                                         (λ x → (Singleton (replay x)))
                                         (λ x → (Singleton (replay x)))
                                         (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                         (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                         (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                         (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                         (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                         (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                         (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                         (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                         (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                            (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                         (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                            (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                         (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                            (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                         (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                            (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                         (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                         (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                         (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-elgamalrsa-path : Interprets the elgamalrsa-enc path in cryptR as a path in the Universe given by ElGamal-encrypt function --}
I-cryptR-elgamalrsa-enc : {n : Nat} → (p : Nat) → (r : History 0 n) →
                          ap I-cryptR (elgamalrsa-enc p r) ≡ ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                  (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p))))
I-cryptR-elgamalrsa-enc p r = βreccryptR-ElgRSAE Set (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                                     (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                   (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                   (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                   (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                   (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                     (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                                     (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-elgamalrsa-dec : Interprets the elgamalrsa-dec path in cryptR as a path in the Universe given by ElGamal-decrypt function --}
I-cryptR-elgamalrsa-dec : {n : Nat} → (p : Nat) → (r : History 0 n) →
                          ap I-cryptR (elgamalrsa-dec p r) ≡ ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                      (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p))))
I-cryptR-elgamalrsa-dec p r = βreccryptR-ElgRSAD Set (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                                     (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                   (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                   (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                   (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                   (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                     (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                                     (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-elgamalope-enc : Interprets the elgamalope-enc path in cryptR as a path in the Universe given by ElGamal-encrypt function --}
I-cryptR-elgamalope-enc : {n : Nat} → (p : Nat) → (r : History 0 n) →
                           ap I-cryptR (elgamalope-enc p r) ≡ ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                  (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p))))
I-cryptR-elgamalope-enc p r = βreccryptR-ElgOPEE Set (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                                     (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                   (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                   (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                   (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                   (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                     (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                                     (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-elgamalope-dec : Interprets the elgamalope-dec path in cryptR as a path in the Universe given by ElGamal-decrypt function --}
I-cryptR-elgamalope-dec : {n : Nat} → (p : Nat) → (r : History 0 n) →
                          ap I-cryptR (elgamalope-dec p r) ≡ ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                      (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p))))
I-cryptR-elgamalope-dec p r = βreccryptR-ElgOPED Set (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ x → (Singleton (replay x)))
                                                     (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                                     (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                   (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                   (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                   (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                   (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                     (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                                     (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-increment100-path : Interprets the increment-by-100 path in cryptR as a path in the Universe given by increment-100 function --}
I-cryptR-increment100-path : {n : Nat} → (i : Nat) → (r : History 0 n) →
                             ap I-cryptR (increment-by-100 i r) ≡ ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i)))
I-cryptR-increment100-path i r = βreccryptR-increment100 Set (λ x → (Singleton (replay x)))
                                                              (λ x → (Singleton (replay x)))
                                                              (λ x → (Singleton (replay x)))
                                                              (λ x → (Singleton (replay x)))
                                                              (λ x → (Singleton (replay x)))
                                                              (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                                              (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                                              (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                                              (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                                              (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                                              (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                                              (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                                              (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                                              (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                            (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                              (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                            (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                              (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                            (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                              (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                            (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                              (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                                              (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                                              (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-crypt-increment100-path : Interprets the crypt-increment-by-100 path in cryptR as a path in the Universe given by crypt-increment-100 function --}
I-cryptR-crypt-increment100-path : {n : Nat} → (p q : Nat) → (i : Nat) → (r : History 0 n) →
                                   ap I-cryptR (crypt-increment-by-100 p q i r) ≡ ua (singleton-equiv {List Int} {List Int}
                                                                                                         {(crypt-increment-100 p q i)}
                                                                                                         (to-Singleton (crypt-increment-100 p q i)))
I-cryptR-crypt-increment100-path p q i r = βreccryptR-crypt-inc Set (λ x → (Singleton (replay x)))
                                                                     (λ x → (Singleton (replay x)))
                                                                     (λ x → (Singleton (replay x)))
                                                                     (λ x → (Singleton (replay x)))
                                                                     (λ x → (Singleton (replay x)))
                                                                     (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                                                     (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                                                     (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                                   (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                                   (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                                                   (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                                                     (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                                                   (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                                                     (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                                                     (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                                                     (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))

{-- I-cryptR-id : Identity function for cryptR --}
I-cryptR-id : {n : Nat} → (r : History 0 n) → ap I-cryptR (id-cryptR r) ≡ ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id))
I-cryptR-id r = βreccryptR-id Set (λ x → (Singleton (replay x)))
                                   (λ x → (Singleton (replay x)))
                                   (λ x → (Singleton (replay x)))
                                   (λ x → (Singleton (replay x)))
                                   (λ x → (Singleton (replay x)))
                                   (λ val i r → ua (singleton-equiv {List Int} {List Int} {(insert val i)} (to-Singleton (insert val i))))
                                   (λ i r → ua (singleton-equiv {List Int} {List Int} {(delete i)} (to-Singleton (delete i))))
                                   (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-encrypt p q)} (to-Singleton (rsa-encrypt p q))))
                                   (λ p q r → ua (singleton-equiv {List Int} {List Int} {(rsa-decrypt p q)} (to-Singleton (rsa-decrypt p q))))
                                   (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                   (λ p q r → ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                   (λ r → ua (singleton-equiv {List Int} {List Int} {ope-encrypt} (to-Singleton ope-encrypt)))
                                   (λ r → ua (singleton-equiv {List Int} {List Int} {ope-decrypt} (to-Singleton ope-decrypt)))
                                   (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                       (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                   (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                       (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                   (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-encrypt2 p ○ (ElGamal-encrypt p))}
                                                                                       (to-Singleton (ElGamal-encrypt2 p ○ (ElGamal-encrypt p)))))
                                   (λ p r → ua (singleton-equiv {List Int} {List Int} {(ElGamal-decrypt p ○ (ElGamal-decrypt2 p))}
                                                                                       (to-Singleton (ElGamal-decrypt p ○ (ElGamal-decrypt2 p)))))
                                   (λ i r → ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i))))
                                   (λ p q i r → ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                   (λ r → ua (singleton-equiv {List Int} {List Int} {id} (to-Singleton id)))


{-- Path representing the homotopy of Paillier homomorphic property --}  
paillier-homotopy : {n : Nat} → (p q : Nat) (i : Nat) → (r : History 0 n) →
                      transport (λ x → ctab r ≡ ctab x) (PAILLIER-HOMOMORPHISM p , q , i :: r)
                                ((paillier-enc p q r) ∘
                                (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))))
                      ≡ (increment-by-100 i r)
paillier-homotopy p q i r = transport (λ x → ctab r ≡ ctab x) (PAILLIER-HOMOMORPHISM p , q , i :: r)
                                ((paillier-enc p q r) ∘
                                (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r)))) ≡⟨ transport' ctab_ (PAILLIER-HOMOMORPHISM p , q , i :: r)
                                                                                                                       (((paillier-enc p q r) ∘
                                                                                                                       (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                                                                                                       (paillier-dec p q (CRYPT-INCREMENT100 p , q , i ::
                                                                                                                       (PAILLIER-ENCRYPT p , q :: r))))) ⟩
                                ((paillier-enc p q r) ∘
                                (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r)))) ∘
                                (ap ctab_ (PAILLIER-HOMOMORPHISM p , q , i :: r)) ≡⟨ ap (λ x → ((paillier-enc p q r) ∘
                                                                                                  (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                                                                                  (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r)))) ∘ x)
                                                                                          (paillier-homRecToCDB p q i r) ⟩
                                ((paillier-enc p q r) ∘
                                (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r)))) ∘
                                ! ((paillier-enc p q r) ∘ (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r)))) ∘ (increment-by-100 i r)
                                ≡⟨ assocP ((paillier-enc p q r) ∘
                                            (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                            (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))))
                                          (! ((paillier-enc p q r) ∘
                                              (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                              (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r)))))
                                              (increment-by-100 i r) ⟩
                                (((paillier-enc p q r) ∘
                                (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r)))) ∘
                                ! ((paillier-enc p q r) ∘ (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))))) ∘ (increment-by-100 i r)
                                ≡⟨ ap (λ x → x ∘ (increment-by-100 i r))
                                      (invTransR ((paillier-enc p q r) ∘
                                                  (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                                  (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))))) ⟩
                                refl ∘ (increment-by-100 i r) ≡⟨ ! (unitTransL (increment-by-100 i r)) ⟩
                                (increment-by-100 i r) ∎


{-- I-hom-paillier1 : Maps the part 1 of Paillier homomorphism into the Universe --}
I-hom-paillier1' : {n : Nat} → (p q : Nat) → (i : Nat) → (r : History 0 n) →
                    ap I-cryptR ((paillier-enc p q r) ∘ (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                 (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))))
                    ≡ (ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q))}
                                            (to-Singleton (paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q)))))
I-hom-paillier1' {n} p q i r =  ap I-cryptR ((paillier-enc p q r) ∘ (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                 (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r)))) ≡⟨ apfTrans I-cryptR
                                                                       (paillier-enc p q r) ((crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r) ∘
                                                                       (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))))) ⟩
                                (ap I-cryptR (paillier-enc p q r)) ∘ (ap I-cryptR ((crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))))) ≡⟨ ap (λ x → (ap I-cryptR (paillier-enc p q r)) ∘ x)
                                                                              (apfTrans I-cryptR ((crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)))
                                                                              (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r)))) ⟩
                                ap I-cryptR (paillier-enc p q r) ∘
                                ap I-cryptR (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                ap I-cryptR (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))) ≡⟨ ap
                                                                                            (λ x → x ∘ ap I-cryptR (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                                                                            ap I-cryptR (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))))
                                                                                            (I-cryptR-paillier-enc p q r) ⟩
                                (ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q)))) ∘
                                ap I-cryptR (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                ap I-cryptR (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))) ≡⟨ ap
                                                                                            (λ x → (ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)}
                                                                                                        (to-Singleton (paillier-encrypt p q)))) ∘ x ∘
                                                                                                        ap I-cryptR (paillier-dec p q (CRYPT-INCREMENT100 p , q , i ::
                                                                                                                    (PAILLIER-ENCRYPT p , q :: r))))
                                                                                            (I-cryptR-crypt-increment100-path p q i (PAILLIER-ENCRYPT p , q :: r)) ⟩
                                (ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q)))) ∘
                                (ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i)))) ∘ 
                                ap I-cryptR (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))) ≡⟨ ap
                                                                                            (λ x → (ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)}
                                                                                                        (to-Singleton (paillier-encrypt p q)))) ∘
                                                                                                   (ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)}
                                                                                                       (to-Singleton (crypt-increment-100 p q i)))) ∘ x)
                                                                                            ((I-cryptR-paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r)))) ⟩
                                (ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q)))) ∘
                                (ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i)))) ∘ 
                                (ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                ≡⟨ assocP (ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q))))
                                          (ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))
                                          (ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q)))) ⟩
                                ((ua (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} {(replay r)} (to-Singleton (paillier-encrypt p q)))) ∘
                                (ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} {(replay (PAILLIER-ENCRYPT p , q :: r))} (to-Singleton (crypt-increment-100 p q i))))) ∘ 
                                (ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                ≡⟨ ap (λ x → x ∘ (ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q)))))
                                      (! (ua-∘e' {List Int} {List Int} {List Int} {(paillier-encrypt p q)} {(crypt-increment-100 p q i)} {(replay r)}
                                               (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} (to-Singleton (paillier-encrypt p q)))
                                               (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} (to-Singleton (crypt-increment-100 p q i))))) ⟩
                                (ua (_∘e'_ {List Int} {List Int} {List Int} {(crypt-increment-100 p q i)} {(paillier-encrypt p q)} {(replay r)}
                                           (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i)} {(replay (PAILLIER-ENCRYPT p , q :: r))}
                                                            (to-Singleton (crypt-increment-100 p q i)))
                                           (singleton-equiv {List Int} {List Int} {(paillier-encrypt p q)} {(replay r)} (to-Singleton (paillier-encrypt p q))))) ∘ 
                                (ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                ≡⟨ ap (λ x → x ∘ (ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q)))))
                                      (ap ua refl) ⟩
                                (ua (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i) ○ (paillier-encrypt p q)} {(replay r)}
                                    (to-Singleton ((crypt-increment-100 p q i) ○ (paillier-encrypt p q))))) ∘
                                (ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))
                                ≡⟨ (! (ua-∘e' {List Int} {List Int} {List Int} {(crypt-increment-100 p q i) ○ (paillier-encrypt p q)} {(paillier-decrypt p q)}  {(replay r)}
                                               (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i) ○ (paillier-encrypt p q)} {(replay r)}
                                                               (to-Singleton ((crypt-increment-100 p q i) ○ (paillier-encrypt p q))))
                                               (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q))))) ⟩
                                (ua (_∘e'_ {List Int} {List Int} {List Int} {(paillier-decrypt p q)} {(crypt-increment-100 p q i) ○ (paillier-encrypt p q)} {(replay r)}
                                           (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q)} (to-Singleton (paillier-decrypt p q)))
                                           (singleton-equiv {List Int} {List Int} {(crypt-increment-100 p q i) ○ (paillier-encrypt p q)}
                                               (to-Singleton ((crypt-increment-100 p q i) ○ (paillier-encrypt p q))))))
                                ≡⟨ ap ua refl ⟩
                                (ua (singleton-equiv {List Int} {List Int} {(paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q))}
                                            (to-Singleton (paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q))))) ∎


{-- I-hom-paillier1 : Maps the part 1 of Paillier homomorphism into the Universe --}

I-hom-paillier1 : {n : Nat} → (p q : Nat) → (i : Nat) → (r : History 0 n) →
                    (transport (λ x → Singleton (replay r) ≡ Singleton (replay x)) (PAILLIER-HOMOMORPHISM p , q , i :: r)
                                 (ap I-cryptR  ((paillier-enc p q r) ∘
                                 (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                 (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))))))
                    ≡ (transport (λ x → Singleton (replay r) ≡ Singleton (replay x)) (PAILLIER-HOMOMORPHISM p , q , i :: r) -- (paillier-hom2* p q i r)
                         (ua (singleton-equiv {List Int} {List Int}
                                           {(paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q))}
                                           (to-Singleton (paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q))))))
I-hom-paillier1 p q i r = (transport (λ x → Singleton (replay r) ≡ Singleton (replay x)) (PAILLIER-HOMOMORPHISM p , q , i :: r)
                                 (ap I-cryptR  ((paillier-enc p q r) ∘
                                 (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                 (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))))))
                    ≡⟨ ap (transport (λ x → Singleton (replay r) ≡ Singleton (replay x)) (PAILLIER-HOMOMORPHISM p , q , i :: r)) (I-hom-paillier1' p q i r) ⟩
                    (transport (λ x → Singleton (replay r) ≡ Singleton (replay x)) (PAILLIER-HOMOMORPHISM p , q , i :: r)
                         (ua (singleton-equiv {List Int} {List Int}
                                           {(paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q))}
                                           (to-Singleton (paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q)))))) ∎

{-- I-hom-paillier2 : Maps the part 2 of Paillier homomorphism into the Universe --}
I-hom-paillier2 : {n : Nat} → (i : Nat) → (r : History 0 n) → ap I-cryptR (increment-by-100 i r) ≡ ua (singleton-equiv {List Int} {List Int} {(increment-100 i)}
                                                                                                         (to-Singleton (increment-100 i)))
I-hom-paillier2 i r = I-cryptR-increment100-path i r


postulate
  {-- Paillier homomorphism --}
  paillier-hom* : {n : Nat} → (p q : Nat) → (i : Nat) → (r : History 0 n) →  (Singleton ((paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q)) (replay r))) ≡
                                                                                       (Singleton ((increment-100 i) (replay r)))


{-- paillier-hom : Representation of Paillier homomorphism in the Universe --}
paillier-hom : {n : Nat} → (p q : Nat) → (i : Nat) → (r : History 0 n) →
                  (transport (λ x → Singleton (replay r) ≡ Singleton (replay x)) (PAILLIER-HOMOMORPHISM p , q , i :: r) 
                     (ua (singleton-equiv {List Int} {List Int}
                                          {(paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q))}
                                          (to-Singleton (paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q))))))
                 ≡  (ua (singleton-equiv {List Int} {List Int}
                                          {(increment-100 i)}
                                          (to-Singleton (increment-100 i))))
paillier-hom p q i r = (transport (λ x → Singleton (replay r) ≡ Singleton (replay x)) (PAILLIER-HOMOMORPHISM p , q , i :: r) 
                                  (ua (singleton-equiv {List Int} {List Int}
                                      {(paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q))}
                                      (to-Singleton (paillier-decrypt p q ○ (crypt-increment-100 p q i) ○ (paillier-encrypt p q)))))) ≡⟨ ! (I-hom-paillier1 p q i r) ⟩
                                  (transport (λ x → Singleton (replay r) ≡ Singleton (replay x)) (PAILLIER-HOMOMORPHISM p , q , i :: r)
                                             (ap I-cryptR  ((paillier-enc p q r) ∘
                                                            (crypt-increment-by-100 p q i (PAILLIER-ENCRYPT p , q :: r)) ∘
                                                            (paillier-dec p q (CRYPT-INCREMENT100 p , q , i :: (PAILLIER-ENCRYPT p , q :: r))))))
                                                            ≡⟨ ap' (ap I-cryptR) {(PAILLIER-HOMOMORPHISM p , q , i :: r)} (paillier-homotopy p q i r) ⟩
                                  (ap I-cryptR (increment-by-100 i r)) ≡⟨ (I-hom-paillier2 i r) ⟩
                                  (ua (singleton-equiv {List Int} {List Int} {(increment-100 i)} (to-Singleton (increment-100 i)))) ∎

postulate

  {-- I-cryptR-paillier-homotopy : Mapping of the Paillier homomorphism homotopy in cryptR into the Universe given by paillier-hom --}
  I-cryptR-paillier-homotopy : {n : Nat} → (p q : Nat) → (i : Nat) → (r : History 0 n) → 
                                 (ap' (ap I-cryptR) {(PAILLIER-HOMOMORPHISM p , q , i :: r)} (paillier-homotopy p q i r))
                                 ≡
                                 (I-hom-paillier1 p q i r) ∘ (paillier-hom p q i r) ∘ ! (I-hom-paillier2 i r)

{-- Interpreters which converts the given queries into functions acting on types in the Universe --}

{-- Interpreters to map the paths into the Universe --}

interp#1 : {a b : cryptR} → (p : a ≡ b) → (I-cryptR a) ≃ (I-cryptR b)
interp#1 p = coe-biject (ap I-cryptR p) 

interp#2 : {a b : cryptR} → (p : a ≡ b) → (I-cryptR a) → (I-cryptR b)
interp#2 p = coe' (ap I-cryptR p) 

{-- Interpreters to map the homotopies into the Universe --}

interp#3 : {a b : cryptR} → {p q : a ≡ b} → (x : p ≡ q) → (I-cryptR a ≡ I-cryptR b) ≃ (I-cryptR a ≡ I-cryptR b)
interp#3 {a} {b} {p} {q} x = coe-biject (apI-path I-cryptR x)

interp#4 : {a b : cryptR} → {p q : a ≡ b} → (x : p ≡ q) → (I-cryptR a ≡ I-cryptR b) → (I-cryptR a ≡ I-cryptR b)
interp#4 x = coe' (apI-path I-cryptR x)


