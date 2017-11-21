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
open import Automation.reflectionUtils
open import Automation.generateInd

module Automation.test_Induction where

cong : ∀ {a b}{A : Set a}{B : Set b}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

sym : ∀ {a}{A : Set a}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {a}{A : Set a}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

macro
  thm-prv : (C : Name) → Term → TC ⊤
  thm-prv C hole = bindTC (getType C)
                          (λ type → unify hole type)

{--
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
--}

unquoteDecl indNat = generateInd (vArg indNat)
                                 (quote Nat) []


indℕ : (n : Nat) → (C : Nat → Set) → C 0 → ((n : Nat) → C n → C (suc n)) → C n
indℕ 0 C z f = z
indℕ (suc n) C z f = f n (indℕ n C z f)

thm1 : thm-prv indℕ ≡ thm-prv indNat
thm1 = refl

recNat : Nat → (C : Set) → C → (Nat → C → C) → C
recNat 0 C c f = c
recNat (suc n) C c f = f n (recNat n C c f)

add : Nat → Nat → Nat
add = (λ x → recNat x (Nat → Nat) (λ n → n) (λ m r → λ n → suc (r n)))

add-assoc : (i j k : Nat) → add i (add j k) ≡ add (add i j) k
add-assoc = (λ x → indNat x
                      (λ i → (j k : Nat) → add i (add j k) ≡ add (add i j) k)
                      (λ j k → refl)
                      (λ i i+[j+k]≡[i+j]+k j k → cong suc (i+[j+k]≡[i+j]+k j k)))

add-right-unit : (i : Nat) → add i 0 ≡ i
add-right-unit = (λ x → indNat x (λ i → add i 0 ≡ i) refl (λ i i+0≡i → cong suc i+0≡i)) 

add-suc : (i j : Nat) → suc (add i j) ≡ add i (suc j)
add-suc = (λ x → indNat x (λ i → (j : Nat) → suc (add i j) ≡ add i (suc j))
                    (λ j → refl)
                    (λ i s[i+j]≡i+s[j] j → cong suc (s[i+j]≡i+s[j] j)))

add-comm : (i j : Nat) → add i j ≡ add j i
add-comm = (λ x → indNat x
                     (λ i → (j : Nat) → add i j ≡ add j i)
                     (λ j → sym (add-right-unit j))
                     (λ i i+j≡j+i j → trans (cong suc (i+j≡j+i j)) (add-suc j i)))

-- -------

{--
data Vec {a} (A : Set a) : ℕ → Set a where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)
--}

unquoteDecl indVec = generateInd (vArg indVec)
                                 (quote Vec) (0 ∷ 1 ∷ []) -- pass index length of constructors explicitly when it differs from index length of the type

indVec' : {a : Level} → {A : Set a} → {n : Nat} → (xs : Vec A n) → (C : {n : Nat} → Vec A n → Set) → 
         C [] →  ({m : Nat} → (x : A) → (xs : Vec A m) → C xs → C (x ∷ xs)) → C xs
indVec' [] C cnil ccons = cnil
indVec' (x ∷ xs) C cnil ccons = ccons x xs (indVec xs C cnil ccons)
 
thm2 : thm-prv indVec
thm2 = indVec'

-- -------

{--
data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A
--}

unquoteDecl indList = generateInd (vArg indList)
                                  (quote List) []

indList' : {a : Level} → {A : Set a} → (xs' : List A) → (C : List A → Set) → C [] → 
         ((x : A) → (xs : List A) → C xs → C (x ∷ xs)) → C xs'
indList' [] C cnil ccons = cnil
indList' (x ∷ xs) C cnil ccons = ccons x xs (indList' xs C cnil ccons)

thm3 : thm-prv indList
thm3 = indList'

-- -------

{--
data Fin : Nat → Set where
  zero : ∀ {n} → Fin (suc n) 
  suc : ∀ {n} → Fin n → Fin (suc n)
--}

unquoteDecl indFin = generateInd (vArg indFin)
                                 (quote Fin) []

indFin' : {n : Nat} → (xs : Fin n) → (C : {n : Nat} → Fin n → Set) → ({n : Nat} → C {(suc n)} zero) →
          ({n : Nat} → (x : Fin n) → C {n} x → C {(suc n)} (suc x)) → C xs
indFin' (Fin.zero {n}) C cnil csuc = cnil
indFin' (Fin.suc {n} x) C cnil csuc = csuc x (indFin' x C cnil csuc)

thm4 : thm-prv indFin' ≡ thm-prv indFin
thm4 = refl

-- -------

{--
data Bool : Set where
  false true : Bool
--}

unquoteDecl indBool = generateInd (vArg indBool)
                                  (quote Bool) []

indBool' : (b : Bool) → (C : Bool → Set) → C false → C true → C b
indBool' false C el th = el
indBool' true C el th = th

thm5 : thm-prv indBool' ≡ thm-prv indBool
thm5 = refl

-- --------

data W (A : Set) (B : A → Set) : Set where
   sup : (a : A) → (B a → W A B) → W A B

unquoteDecl indW = generateInd
                   (vArg indW)
                   (quote W) []

indW' : {A : Set} {B : A → Set} → (c : W A B) → (C : W A B → Set) → ((x : A) → (y : B x → W A B) → (z : (v : B x) → C (y v)) → C (sup x y)) → C c
indW' {A} {B} (sup a b) C csup = csup a b (λ v -> indW' {A} {B} (b v) C csup)

thm6 : thm-prv indW ≡ thm-prv indW'
thm6 = refl
