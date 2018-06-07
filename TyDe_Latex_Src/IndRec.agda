-- Here's an example of manually-written induction and recursion rules
-- that follow the spec in the paper. This is useful for comparing
-- against the math in the paper.
module IndRec where

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

data Vec (A : Set) : Nat → Set where
  nil : Vec A zero
  cons : forall {n} -> A -> Vec A n -> Vec A (succ n)

recVec : (A : Set) ->
         (n : Nat) -> Vec A n ->
         (C : Set) ->
         C ->
         ((n : Nat) -> A -> Vec A n -> C -> C) ->
         C
recVec A .zero nil C b s =
  b
recVec A (.succ k) (cons x xs) C b s =
  s k x xs (recVec A k xs C b s)

indVec : (A : Set) ->
         (n : Nat) -> (tgt : Vec A n) ->
         (mot : (k : Nat) -> Vec A k -> Set) ->
         (b : mot zero nil) ->
         (s : (k : Nat) -> (x : A) -> (xs : Vec A k) -> (mot k xs) -> mot (succ k) (cons x xs)) ->
         mot n tgt
indVec A .zero nil mot b s =
  b
indVec A (.succ k) (cons x xs) mot b s =
  s k x xs (indVec A k xs mot b s)



data W (A : Set) (B : A -> Set) : Set where
  sup : (x : A) (f : B x -> W A B) -> W A B

recW : ∀ {A B}
       (tgt : W A B) →
       (C : Set) →
       (step : (x : A) → (f : B x → W A B) → (f' : (b : B x) → C) → C) →
       C
recW (sup x f) C step =
  step x f (λ b → recW (f b) C step)


indW : (A : Set) -> (B : A -> Set) ->
       (tgt : W A B) ->
       (mot : W A B -> Set) ->
       (f-sup : (x : A) -> (f : B x -> W A B) -> (f' : (b : B x) -> mot (f b)) -> mot (sup x f)) ->
       mot tgt
indW A B (sup x f) mot f-sup =
  f-sup x f (λ b -> indW A B (f b) mot f-sup)


-- Proof of concept - proving the induction principle on Nat using W

data Bool : Set where
  tt ff : Bool

record Unit : Set where
  constructor unit

data Void : Set where


Tag : Bool -> Set
Tag tt = Unit
Tag ff = Void

wNat : Set
wNat = W Bool Tag

wz : wNat
wz = sup ff λ ()

ws : wNat -> wNat
ws k = sup tt (λ _ -> k)

data _≡_ {A : Set} (x : A) : A -> Set where
  refl : x ≡ x

subst : {A : Set} (mot : A -> Set) -> {x y : A} -> (p : x ≡ y) -> mot x -> mot y
subst mot refl b = b

postulate
  funext : {A B : Set} (f g : A -> B) -> ((x : A) -> f x ≡ g x) -> f ≡ g

wNatInd : (tgt : wNat) ->
          (mot : wNat -> Set) ->
          (b : mot wz) ->
          (s : (k : wNat) -> mot k -> mot (ws k)) ->
          mot tgt
wNatInd tgt mot b s =
  indW Bool Tag tgt mot λ
   { tt -> λ f ih -> s (f unit) (ih unit)
   ; ff -> λ f k -> let wz=supf : wz ≡ sup ff f
                        wz=supf = subst (λ f -> wz ≡ sup ff f) (funext (λ ()) f λ ()) refl
                    in subst mot wz=supf b
   }
