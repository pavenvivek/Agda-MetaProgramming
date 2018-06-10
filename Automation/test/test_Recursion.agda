-- {-# OPTIONS --verbose tc.unquote.decl:20 #-}
-- {-# OPTIONS --verbose tc.unquote.def:10 #-}
-- {-# OPTIONS --verbose tc.term.expr.top:5 #-}
-- {-# OPTIONS --verbose tc.sample.debug:12 #-}

open import Agda.Builtin.Reflection
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Primitive
open import Data.List
open import Data.Vec
open import Data.Fin
open import Automation.utils.reflectionUtils
open import Automation.lib.generateRec

module Automation.test.test_Recursion where

macro
  thm-prv : (C : Name) → Term → TC ⊤
  thm-prv C hole = bindTC (getType C)
                          (λ type → unify hole type)

{--
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
--}

unquoteDecl recNat = generateRec (vArg recNat)
                                 (quote Nat)

double : Nat → Nat
double = (λ x → recNat x Nat 0 (λ n r → suc (suc r)))

add : Nat → Nat → Nat
add = (λ x → recNat x (Nat → Nat) (λ n → n) (λ m r → λ n → suc (r n)))

recℕ : Nat → (C : Set) → C → (Nat → C → C) → C
recℕ 0 C c f = c
recℕ (suc n) C c f = f n (recℕ n C c f)

thm1 : thm-prv recℕ ≡ thm-prv recNat
thm1 = refl

-- --------

{--
data Vec {a} (A : Set a) : ℕ → Set a where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)
--}

unquoteDecl recVec = generateRec (vArg recVec)
                                 (quote Vec) 

recVec' : ∀{a} {A : Set a} → {n : Nat} → Vec A n → (C : Set) → C → 
         ({m : Nat} → (x : A) → (xs : Vec A m) → C → C) → C
recVec' [] C cnil ccons = cnil
recVec' (x ∷ xs) C cnil ccons = ccons x xs (recVec' xs C cnil ccons)
 
thm2 : thm-prv recVec
thm2 = recVec'

-- --------

{--
data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A
--}

unquoteDecl recList = generateRec (vArg recList)
                                  (quote List)

recList' : ∀{a} {A : Set a} → List A → (C : Set) → C → 
         ((x : A) → (xs : List A) → C → C) → C
recList' [] C cnil ccons = cnil
recList' (x ∷ xs) C cnil ccons = ccons x xs (recList' xs C cnil ccons)

thm3 : thm-prv recList
thm3 = recList'

-- --------

{--
data Fin : Nat → Set where
  zero : ∀ {n} → Fin (suc n) 
  suc : ∀ {n} → Fin n → Fin (suc n)
--}

unquoteDecl recFin = generateRec (vArg recFin)
                                 (quote Fin)

recFin' : {n : Nat} → (xs : Fin n) → (C : Set) → (cnil : C) → -- (cnil : {n : Nat} → C) →
         (csuc : {n : Nat} → (x : Fin n) → C → C) → C
recFin' (Fin.zero {n}) C cnil csuc = cnil
recFin' (Fin.suc {n} x) C cnil csuc = csuc {n} x (recFin' x C cnil csuc)

thm4 : thm-prv recFin' ≡ thm-prv recFin
thm4 = refl

-- --------

{--
data Bool : Set where
  false true : Bool
--}

unquoteDecl recBool = generateRec (vArg recBool)
                                  (quote Bool)
                                  
recBool' : Bool → (C : Set) → C → C → C
recBool' false C el th = el
recBool' true C el th = th

thm5 : thm-prv recBool' ≡ thm-prv recBool
thm5 = refl

-- --------

data W (A : Set) (B : A → Set) : Set where
   sup : (a : A) → (B a → W A B) → W A B

unquoteDecl recW = generateRec
                   (vArg recW)
                   (quote W)

recW' : {A : Set} {B : A → Set} → W A B → (C : Set) → ((x : A) → (B x → W A B) → (z : B x → C ) → C) → C
recW' {A} {B} (sup a b) C csup = csup a b (λ v → recW' {A} {B} (b v) C csup)

thm6 : thm-prv recW ≡ thm-prv recW'
thm6 = refl


