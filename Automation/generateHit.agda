-- {-# OPTIONS --verbose tc.unquote.decl:20 #-}
-- {-# OPTIONS --verbose tc.unquote.def:10 #-}
-- {-# OPTIONS --verbose tc.term.expr.top:5 #-}
-- {-# OPTIONS --verbose tc.sample.debug:12 #-}
-- {-# OPTIONS --type-in-type #-}

open import Agda.Builtin.Reflection
open import Agda.Primitive
open import Data.List
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Data.Empty
open import Automation.reflectionUtils

module Automation.generateHit where

data ArgPath {ℓ₁} : Set (lsuc ℓ₁) where
  argPath : Set ℓ₁ → ArgPath


getHdType : (baseType : Name) → (indType : Name) → (consType : Type) → TC Type
getHdType baseType indType (pi (arg info dom) (abs s cdom)) = bindTC (getHdType baseType indType cdom)
                                                                     (λ cdom' → bindTC (getHdType baseType indType dom)
                                                                     (λ dom' → returnTC (pi (arg info dom') (abs s cdom'))))
getHdType baseType indType (def ty y) = bindTC (returnTC (primQNameEquality ty baseType)) λ
                                               { true → returnTC (def indType y) ;
                                                 false → returnTC (def ty y) }
getHdType baseType indType x = returnTC unknown 

defineHitCons : Name → Name → List Name → List Name → TC ⊤
defineHitCons base ind (x ∷ xs) (y ∷ ys) = bindTC (defineHitCons base ind xs ys) λ _ →
                                           bindTC (getType x) λ ty →
                                           bindTC (getHdType base ind ty) λ ty' →
                                           bindTC (declareDef (vArg y) ty') λ _ →
                                           (defineFun y (clause [] (con x []) ∷ []))
defineHitCons base ind x y = returnTC tt

defineHitPathCons : (paths : List Name) → (pathTypes : List Type) → TC ⊤
defineHitPathCons (x ∷ xs) (ty ∷ tys) = bindTC (defineHitPathCons xs tys) λ _ →
                                               (declarePostulate (vArg x) ty)
defineHitPathCons x ty = returnTC tt

{-# TERMINATING #-}
changeBaseCtrs : (baseType : Name) → (indType : Name) → (baseCtrs : List Name) → (hindCtrs : List Name) → Term → TC Term
changeBaseCtrs base ind ctrs ictrs (con x args) = bindTC (checkName x ctrs) λ
                                         { true → bindTC (getCtrIndex 0 x ctrs)
                                                         (λ i → bindTC (getListElement' i ictrs)
                                                         (λ ctr' → bindTC (debugPrint "tc.sample.debug" 12 (termErr (con x []) ∷ strErr "and" ∷ termErr (def ctr' []) ∷ [])) 
                                                         (λ _ → bindTC (map' (λ { (arg i term) → bindTC (changeBaseCtrs base ind ctrs ictrs term)
                                                                                                         (λ term' → returnTC (arg i term')) }) args)
                                                         (λ args' → returnTC (def ctr' args'))))) ;
                                           false → returnTC (con x args) }
changeBaseCtrs base ind ctrs ictrs x = returnTC x

qualifyPath : (baseType : Name) → (indType : Name) → (baseCtrs : List Name) → (hindCtrs : List Name) → (args : Term) → TC Type
qualifyPath base ind ctrs ictrs (pi (arg info t1) (abs s t2)) = bindTC (qualifyPath base ind ctrs ictrs t2)
                                                                       (λ t2' → bindTC (returnTC t1) λ
                                                                                       { (def x args) → bindTC (returnTC (primQNameEquality x base)) λ
                                                                                                               { true → returnTC (pi (arg info (def ind args)) (abs s t2')) ;
                                                                                                                 false → returnTC (pi (arg info (def x args)) (abs s t2')) } ;
                                                                                         term' → returnTC (pi (arg info term') (abs s t2')) })
qualifyPath base ind ctrs ictrs (def x args) = bindTC (returnTC (primQNameEquality x (quote _≡_))) λ 
                                  { true → bindTC (map' (λ { (arg (arg-info visible relevant) term) → bindTC (changeBaseCtrs base ind ctrs ictrs term)
                                                                                                              (λ term' → returnTC (vArg term')) ;
                                                              argTerm → returnTC argTerm }) args)
                                                   (λ args' → returnTC (def x args')) ;
                                    false → returnTC (def x args) }
qualifyPath base ind ctrs ictrs x = returnTC x

addArgPath : ∀{ℓ₁} → (baseType : Name) → (indType : Name) → (baseCtrs : List Name) → (hindCtrs : List Name) → ArgPath {ℓ₁} → TC Type
addArgPath base ind ctrs ictrs (argPath argType) = bindTC (quoteTC argType)
                                                   (λ argTyp → qualifyPath base ind ctrs ictrs argTyp )

getPathTypes : ∀{ℓ₁} → (baseType : Name) → (indType : Name) → (baseCtrs : List Name) → (hindCtrs : List Name) → List (ArgPath {ℓ₁}) → TC (List Type)
getPathTypes base ind ctrs ictrs [] = returnTC []
getPathTypes base ind ctrs ictrs (x ∷ xs) = bindTC (getPathTypes base ind ctrs ictrs xs)
                                                   (λ xs' → bindTC (addArgPath base ind ctrs ictrs x)
                                                   (λ x' → returnTC (x' ∷ xs')))

defineHindType : (baseType : Name) → (indType : Name) → TC ⊤
defineHindType baseType indType =
  bindTC (getType baseType) λ ty →
  bindTC (declareDef (vArg indType) ty) λ _ →
  (defineFun indType (clause [] (def baseType []) ∷ []))

definePointHolder : (pointHolder : Name) → (lcons : List Name) → TC ⊤
definePointHolder pointHolder lcons =
  bindTC (quoteTC (List Name)) λ LQName →
  bindTC (declareDef (vArg pointHolder) LQName) λ _ →
  bindTC (quoteTC lcons) λ lconsQ →
  (defineFun pointHolder (clause [] lconsQ ∷ []))

definePathHolder : (pathHolder : Name) → (lpaths : List Name) → TC ⊤
definePathHolder pathHolder lpaths =
  bindTC (quoteTC (List Name)) λ LQName →
  bindTC (declareDef (vArg pathHolder) LQName) λ _ →
  bindTC (quoteTC lpaths) λ lpathsQ →
  (defineFun pathHolder (clause [] lpathsQ ∷ []))

data-hit : ∀{ℓ₁} (baseType : Name) → (indType : Name) → (pointHolder : Name) → (lcons : List Name) → (pathHolder : Name) → (lpaths : List Name) →
                  (lpathTypes : (List (ArgPath {ℓ₁}))) → TC ⊤
data-hit baseType indType pointHolder lcons pathHolder lpaths lpathTypes =
  bindTC (defineHindType baseType indType) λ _ → 
  bindTC (getConstructors baseType) λ lcons'  →
  bindTC (defineHitCons baseType indType lcons' lcons) λ _ →
  bindTC (getPathTypes baseType indType lcons' lcons lpathTypes) λ lpathTypes' →
  bindTC (defineHitPathCons lpaths lpathTypes') λ _ →
  bindTC (definePointHolder pointHolder lcons) λ _ →
  definePathHolder pathHolder lpaths
