-- {-# OPTIONS --verbose tc.unquote.decl:20 #-}
-- {-# OPTIONS --verbose tc.unquote.def:10 #-}
-- {-# OPTIONS --verbose tc.term.expr.top:5 #-}
-- {-# OPTIONS --verbose tc.sample.debug:12 #-}
-- {-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-auto-inline #-}

open import Agda.Builtin.Reflection
open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality
open import Data.List

open import Automation.lib.generateRec
open import Automation.lib.generateInd
open import Automation.lib.generateHit
open import Automation.lib.generateRecHit
open import Automation.lib.generateIndHit
open import Automation.utils.reflectionUtils
open import Automation.utils.pathUtils

module Automation.test.test_HIndTypes where

macro
  thm-prv : (C : Name) → Term → TC ⊤
  thm-prv C hole = bindTC (getType C)
                          (λ type → unify hole type)

module Circle1 where
  private 
    data S₁* : Set where
      base* : S₁*

{--
  S : Set
  S = S*

  base : S
  base = base*

  postulate 
    loop : base ≡ base
--}

  unquoteDecl S₁ S₁points base S₁paths loop = data-hit (quote S₁*) S₁
                                                S₁points (base ∷ []) -- point constructors
                                                S₁paths (loop ∷ []) -- path constructors
                                                (argPath (base* ≡ base*) ∷ []) -- base* will be replaced by base

{--
  recS : S → (C : Set) → (cbase : C) → (cloop : cbase ≡ cbase) → C
  recS base* C cbase cloop = cbase
--}

  unquoteDecl recS₁* = generateRec (vArg recS₁*)
                                   (quote S₁*)

  unquoteDecl recS₁ βrecS₁ = generateRecHit (vArg recS₁) ((vArg βrecS₁) ∷ [])
                                     (quote S₁*)
                                     (quote recS₁*)
                                     (quote S₁) S₁points S₁paths

  thm1 : thm-prv recS₁ ≡ (S₁ → (C : Set) → (cbase : C) → (cloop : cbase ≡ cbase) → C)
  thm1 = refl

{--
  postulate
    βrecS : (C : Set) → (cbase : C) → (cloop : cbase ≡ cbase) → 
      ap (λ x → recS x C cbase cloop) loop ≡ cloop
--}

  thm2 : thm-prv βrecS₁ ≡ ((C : Set) → (cbase : C) → (cloop : cbase ≡ cbase) → ap (λ x → recS₁ x C cbase cloop) loop ≡ cloop)
  thm2 = refl

{--
  indS : (circle : S) → (C : S → Set) → 
    (cbase : C base) → (cloop : transport C loop cbase ≡ cbase) → C circle
  indS base* C cbase cloop = cbase
--}

  unquoteDecl indS₁* = generateInd (vArg indS₁*)
                                   (quote S₁*)

  unquoteDecl indS₁ βindS₁ = generateIndHit (vArg indS₁) ((vArg βindS₁) ∷ [])
                                     (quote S₁*)
                                     (quote indS₁*)
                                     (quote S₁) S₁points S₁paths

  thm3 : thm-prv indS₁ ≡ ((circle : S₁) → (C : S₁ → Set) → (cbase : C base) → (cloop : transport C loop cbase ≡ cbase) → C circle)
  thm3 = refl

{--
  postulate
    βindS : (C : S → Set) → 
      (cbase : C base) → (cloop : transport C loop cbase ≡ cbase) → 
      apd (λ x → indS x C cbase cloop) loop ≡ cloop
--}

  thm4 : thm-prv βindS₁ ≡ ((C : S₁ → Set) → (cbase : C base) → (cloop : transport C loop cbase ≡ cbase) → apd (λ x → indS₁ x C cbase cloop) loop ≡ cloop)
  thm4 = refl

-- ---------

module Circle2 where
  private 
    data S₂* : Set where
      south* : S₂*
      north* : S₂*

{--
  S¹' : Set
  S¹' = S¹'*

  south : S¹'
  south = south*

  north : S¹'
  north = north*

  postulate 
    east : south ≡ north
    west : south ≡ north
--}

  unquoteDecl S₂ S₂points south north S₂paths east west = data-hit (quote S₂*) S₂
                                                            S₂points (south ∷ north ∷ []) -- point constructors
                                                            S₂paths (east ∷ west ∷ []) -- path constructors
                                                            (argPath (south* ≡ north*) ∷ 
                                                             argPath (south* ≡ north*) ∷ []) -- south* and north* will be replaced by south and north resp. 

{--
  recS¹' : S¹' → (C : Set) → 
    (csouth cnorth : C) → (ceast cwest : csouth ≡ cnorth) → C
  recS¹' south* csouth cnorth ceast cwest = csouth
  recS¹' north* csouth cnorth ceast cwest = cnorth
--}

  unquoteDecl recS₂* = generateRec (vArg recS₂*)
                                   (quote S₂*)

  unquoteDecl recS₂ βreceastS₂ βrecwestS₂ = generateRecHit (vArg recS₂) ((vArg βreceastS₂) ∷ (vArg βrecwestS₂) ∷ [])
                                     (quote S₂*)
                                     (quote recS₂*)
                                     (quote S₂) S₂points S₂paths

  thm5 : thm-prv recS₂ ≡ (S₂ → (C : Set) → (csouth cnorth : C) → (ceast cwest : csouth ≡ cnorth) → C)
  thm5 = refl

{--
  postulate
    βreceastS¹' : (C : Set) → 
      (csouth cnorth : C) → (ceast cwest : csouth ≡ cnorth) → 
      ap (λ x → recS¹' x C csouth cnorth ceast cwest) east ≡ ceast
    βrecwestS¹' : (C : Set) → 
      (csouth cnorth : C) → (ceast cwest : csouth ≡ cnorth) → 
      ap (λ x → recS¹' x C csouth cnorth ceast cwest) west ≡ cwest
--}
  thm6 : thm-prv βreceastS₂ ≡ ((C : Set) → (csouth cnorth : C) → (ceast cwest : csouth ≡ cnorth) → ap (λ x → recS₂ x C csouth cnorth ceast cwest) east ≡ ceast)
  thm6 = refl

  thm7 : thm-prv βrecwestS₂ ≡ ((C : Set) → (csouth cnorth : C) → (ceast cwest : csouth ≡ cnorth) → ap (λ x → recS₂ x C csouth cnorth ceast cwest) west ≡ cwest)
  thm7 = refl

{--
  indS¹' : (circle : S¹') → (C : S¹' → Set) → 
    (csouth : C south) → (cnorth : C north) → 
    (ceast : transport C east csouth ≡ cnorth) → 
    (cwest : transport C west csouth ≡ cnorth) → C circle
  indS¹' south* C csouth cnorth ceast cwest = csouth
  indS¹' north* C csouth cnorth ceast cwest = cnorth
--}

  unquoteDecl indS₂* = generateInd (vArg indS₂*)
                                   (quote S₂*)

  unquoteDecl indS₂ βindeastS₂ βindwestS₂ = generateIndHit (vArg indS₂) ((vArg βindeastS₂) ∷ (vArg βindwestS₂) ∷ [])
                                                           (quote S₂*)
                                                           (quote indS₂*)
                                                           (quote S₂) S₂points S₂paths

  thm8 : thm-prv indS₂ ≡ ((circle : S₂) → (C : S₂ → Set) → (csouth : C south) → (cnorth : C north) →  (ceast : transport C east csouth ≡ cnorth) → 
                           (cwest : transport C west csouth ≡ cnorth) → C circle)
  thm8 = refl

{--
  postulate
    βindeastS¹' : (C : S¹' → Set) → 
      (csouth : C south) → (cnorth : C north) → 
      (ceast : transport C east csouth ≡ cnorth) → 
      (cwest : transport C west csouth ≡ cnorth) → 
      apd (λ x → indS¹' x C csouth cnorth ceast cwest) east ≡ ceast
    βindwestS¹' : (C : S¹' → Set) → 
      (csouth : C south) → (cnorth : C north) → 
      (ceast : transport C east csouth ≡ cnorth) → 
      (cwest : transport C west csouth ≡ cnorth) → 
      apd (λ x → indS¹' x C csouth cnorth ceast cwest) west ≡ cwest
--}

  thm9 : thm-prv βindeastS₂ ≡ ((C : S₂ → Set) → (csouth : C south) → (cnorth : C north) → (ceast : transport C east csouth ≡ cnorth) → (cwest : transport C west csouth ≡ cnorth) → 
                                apd (λ x → indS₂ x C csouth cnorth ceast cwest) east ≡ ceast)
  thm9 = refl

  thm10 : thm-prv βindwestS₂ ≡ ((C : S₂ → Set) → (csouth : C south) → (cnorth : C north) → (ceast : transport C east csouth ≡ cnorth) → (cwest : transport C west csouth ≡ cnorth) → 
                                 apd (λ x → indS₂ x C csouth cnorth ceast cwest) west ≡ cwest)
  thm10 = refl

-- ---------

module Pushout where
  private
    data Pushout* {A B C : Set} (f : C → A) (g : C → B) : Set where
      inl* : A → Pushout* f g 
      inr* : B → Pushout* f g

{--
  Pushout : {A B C : Set} → (f : C → A) → (g : C → B) → Set
  Pushout = Pushout*

  inl : {A B C : Set} → {f : C → A} → {g : C → B} → A → Pushout f g
  inl = inl*

  inr : {A B C : Set} → {f : C → A} → {g : C → B} → B → Pushout f g
  inr = inr*

  postulate
    glue : {A B C : Set} → {f : C → A} → {g : C → B} → (c : C) → (inl {A} {B} {C} {f} {g} (f c)) ≡ (inr (g c))
--}

  unquoteDecl Pushout Pushoutpoints inl inr Pushoutpaths glue = data-hit (quote Pushout*) Pushout
                                                                  Pushoutpoints (inl ∷ inr ∷ []) -- point constructors
                                                                  Pushoutpaths (glue ∷ []) -- path constructors
                                                                  (argPath ({A B C : Set} → {f : C → A} → {g : C → B} → (c : C) → (inl* {A} {B} {C} {f} {g} (f c)) ≡ (inr* (g c))) ∷ [])
                                                                  -- inl* and inr* will be replaced by inl and inr respectively

{--
  recPush : {A B C : Set} → {f : C → A} → {g : C → B} →
            Pushout f g → (D : Set) → (f1 : A → D) → (f2 : B → D) →
            (dglue : (c : C) → (f1 (f c)) ≡ (f2 (g c))) → D
  recPush (inl* a) D f1 f2 dglue = (f1 a)
  recPush (inr* b) D f1 f2 dglue = (f2 b)
--}

  unquoteDecl recPush* = generateRec (vArg recPush*)
                                     (quote Pushout*)

  unquoteDecl recPush βrecPush = generateRecHit (vArg recPush) ((vArg βrecPush) ∷ [])
                                       (quote Pushout*)
                                       (quote recPush*)
                                       (quote Pushout) Pushoutpoints Pushoutpaths

  thm11 : thm-prv recPush ≡ ({A B C : Set} → {f : C → A} → {g : C → B} → Pushout f g → (D : Set) → (f1 : A → D) → (f2 : B → D) → (dglue : (c : C) → (f1 (f c)) ≡ (f2 (g c))) → D)
  thm11 = refl

{--
  postulate
    βrecPush' : {A B C : Set} → {f : C → A} → {g : C → B} →
               (D : Set) → (f1 : A → D) → (f2 : B → D) →
               (dglue : (c : C) → (f1 (f c)) ≡ (f2 (g c))) →
               {c : C} → ap (λ x → recPush2 x D f1 f2 dglue) (P2glue {A} {B} {C} {f} {g} c) ≡ (dglue c)
--}

  thm12 : thm-prv βrecPush ≡ ({A B C : Set} → {f : C → A} → {g : C → B} → (D : Set) → (f1 : A → D) → (f2 : B → D) → (dglue : (c : C) → (f1 (f c)) ≡ (f2 (g c))) →
                               {c : C} → ap (λ x → recPush x D f1 f2 dglue) (glue {A} {B} {C} {f} {g} c) ≡ (dglue c))
  thm12 = refl

{--
  indPush : {A B C : Set} → {f : C → A} → {g : C → B} →
            (p : Pushout f g) → (D : Pushout f g → Set) → (f1 : (a : A) → D (inl a)) → (f2 : (b : B) → D (inr b)) →
            (dglue : (c : C) → transport D (glue c) (f1 (f c)) ≡ (f2 (g c))) → D p
  indPush (inl* a) D f1 f2 dglue = (f1 a)
  indPush (inr* b) D f1 f2 dglue = (f2 b)
--}

  unquoteDecl indPush* = generateInd (vArg indPush*)
                                     (quote Pushout*)

  unquoteDecl indPush βindPush = generateIndHit (vArg indPush) ((vArg βindPush) ∷ [])
                                                (quote Pushout*)
                                                (quote indPush*)
                                                (quote Pushout) Pushoutpoints Pushoutpaths

  thm13 : thm-prv indPush ≡ ({A B C : Set} → {f : C → A} → {g : C → B} → (p : Pushout f g) → (D : Pushout f g → Set) → (f1 : (a : A) → D (inl a)) → (f2 : (b : B) → D (inr b)) →
                              (dglue : (c : C) → transport D (glue c) (f1 (f c)) ≡ (f2 (g c))) → D p)
  thm13 = refl

{--
  postulate
    βindPush : {A B C : Set} → {f : C → A} → {g : C → B} →
               (D : Pushout f g → Set) → (f1 : (a : A) → D (inl a)) → (f2 : (b : B) → D (inr b)) →
               (dglue : (c : C) → transport D (glue c) (f1 (f c)) ≡ (f2 (g c))) →
               {c : C} → apd (λ x → indPush x D f1 f2 dglue) (glue c) ≡ (dglue c)
--}

  thm14 : thm-prv βindPush ≡ ({A B C : Set} → {f : C → A} → {g : C → B} → (D : Pushout f g → Set) → (f1 : (a : A) → D (inl a)) → (f2 : (b : B) → D (inr b)) →
                               (dglue : (c : C) → transport D (glue c) (f1 (f c)) ≡ (f2 (g c))) → {c : C} → apd (λ x → indPush x D f1 f2 dglue) (glue c) ≡ (dglue c))
  thm14 = refl

-- ---------

module Susp where

  private
    data Σₛ* (A : Set) : Set where
      N* : Σₛ* A
      S* : Σₛ* A

{--
  Σₛ : (A : Set) → Set
  Σₛ = Σₛ*

  N : {A : Set} → Σₛ A
  N = N*

  S : {A : Set} → Σₛ A
  S = S*

  postulate
    merid : {A : Set} → (a : A) → (N {A} ≡ S {A})
--}

  unquoteDecl Σₛ Σₛpoints N S Σₛpaths merid = data-hit (quote Σₛ*) Σₛ
                                               Σₛpoints (N ∷ S ∷ []) -- point constructors
                                               Σₛpaths (merid ∷ []) -- path constructors
                                               (argPath ({A : Set} → (a : A) → (N* {A} ≡ S* {A})) ∷ []) -- N* and S* will be replaced by N and S resp.

{--
  recₛ : {A : Set} → Σₛ A → (B : Set) → (n s : B) → (m : A → (n ≡ s)) → B
  recₛ N* B n s m = n
  recₛ S* B n s m = s
--}

  unquoteDecl recΣₛ* = generateRec (vArg recΣₛ*)
                                   (quote Σₛ*)

  unquoteDecl recΣₛ βrecΣₛ = generateRecHit (vArg recΣₛ) ((vArg βrecΣₛ) ∷ [])
                                     (quote Σₛ*)
                                     (quote recΣₛ*)
                                     (quote Σₛ) Σₛpoints Σₛpaths

  thm15 : thm-prv recΣₛ ≡ ({A : Set} → Σₛ A → (B : Set) → (n s : B) → (m : A → (n ≡ s)) → B)
  thm15 = refl

{--
  postulate
    βrecₛ : {A : Set} → (B : Set) → (n s : B) → (m : A → (n ≡ s)) →
            {a : A} → ap (λ x → recₛ x B n s m) (merid a) ≡ m a
--}

  thm16 : thm-prv βrecΣₛ ≡ ({A : Set} → (B : Set) → (n s : B) → (m : A → (n ≡ s)) → {a : A} → ap (λ x → recΣₛ x B n s m) (merid a) ≡ m a)
  thm16 = refl

{--
  indₛ : {A : Set} → (x : Σₛ A) → (B : Σₛ A → Set) → (n : B (N {A})) → (s : B (S {A})) → (m : (a : A) → (transport B (merid a) n ≡ s)) → B x
  indₛ N* B n s m = n
  indₛ S* B n s m = s
--}

  unquoteDecl indΣₛ* = generateInd (vArg indΣₛ*)
                                   (quote Σₛ*)

  unquoteDecl indΣₛ βindΣₛ = generateIndHit (vArg indΣₛ) ((vArg βindΣₛ) ∷ [])
                                            (quote Σₛ*)
                                            (quote indΣₛ*)
                                            (quote Σₛ) Σₛpoints Σₛpaths

  thm17 : thm-prv indΣₛ ≡ ({A : Set} → (x : Σₛ A) → (B : Σₛ A → Set) → (n : B (N {A})) → (s : B (S {A})) → (m : (a : A) → (transport B (merid a) n ≡ s)) → B x)
  thm17 = refl

{--
  postulate
    βindₛ : {A : Set} → (B : Σₛ A → Set) → (n : B N) → (s : B S) → (m : (a : A) → (transport B (merid a) n ≡ s)) →
            {a : A} → apd (λ x → indₛ x B n s m) (merid a) ≡ m a  
--}

  thm18 : thm-prv βindΣₛ ≡ ({A : Set} → (B : Σₛ A → Set) → (n : B N) → (s : B S) → (m : (a : A) → (transport B (merid a) n ≡ s)) →
                            {a : A} → apd (λ x → indΣₛ x B n s m) (merid a) ≡ m a)
  thm18 = refl

