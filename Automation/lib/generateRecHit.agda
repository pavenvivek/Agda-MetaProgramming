-- {-# OPTIONS --verbose tc.sample.debug:20 #-}

open import Data.List
open import Function hiding (flip)
open import Agda.Builtin.Reflection
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Automation.utils.reflectionUtils
open import Automation.utils.pathUtils
open import Automation.lib.generateRec using (getMapConstructorType; generateRec)

module Automation.lib.generateRecHit where

getPathClause : (lpoints : Nat) → (lpaths : Nat) → (baseRec : Name) → TC (List Clause)
getPathClause lpoints lpaths baseRec =
  do vars' ← (getClauseVars zero (lpoints + lpaths))
     vars ← (reverseTC vars')
     args ← (generateRef (suc (suc lpoints))) -- +1 for "C" and +1 for constructor
     args' ← (pure (map (λ z → z + lpaths) args))
     argTerms ← (generateRefTerm args')
     pure ((clause (vArg (var "x") ∷ vArg (var "C1") ∷ vars) (def baseRec argTerms)) ∷ [])

getMapConsTypeList' : Name → (Cref : Nat) → (paths : Type) → (pars : List Nat) → (indexList : List Nat) → (lcons : List Name) → TC Type
getMapConsTypeList' R Cref paths pars i [] = pure paths
getMapConsTypeList' R Cref paths pars (i ∷ is) (x ∷ xs) =
  do d ← (getParameters R)
     ty ← (getType x)
     x' ← (rmPars d ty)
     pars' ← (pure (map (λ z → z + 1) pars))
     lb ← (getIndexRef R i x)
     case! (isMemberBool true lb) of λ
      { true →
        do t ← (getMapConstructorType Cref pars R true x')
           xt ← (getMapConsTypeList' R (suc Cref) paths pars' is xs)
           pure (pi (vArg t) (abs "_" xt))
      ; false →
        do x'' ← (rmIndex i x')
           t ← (getMapConstructorType Cref pars R true x'')
           xt ← (getMapConsTypeList' R (suc Cref) paths pars' is xs)
           pure (pi (vArg t) (abs "_" xt))
      }
getMapConsTypeList' R Cref paths pars x y = pure unknown -- Invalid case


{-# TERMINATING #-}
getMapConstructorPathType' : (baseRec : Name) → (pars : List Nat) → (cons : List Nat) → (index : List Nat) →
  (args : List Nat) → (indTyp : Name) → (recurse : Bool) → Type → TC Type
getMapConstructorPathType' baseRec pars cons index args indTyp rcu (pi (arg info t1) (abs s t2)) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
         index' = (map (λ z → z + 1) index)
         args' = (map (λ z → z + 1) args)
         args'' = (args' ∷L 0)
     t1' ← (getMapConstructorPathType' baseRec pars cons index args indTyp rcu t1)
     t2' ← (getMapConstructorPathType' baseRec pars' cons' index' args'' indTyp rcu t2)
     pure (pi (arg info t1') (abs s t2'))
getMapConstructorPathType' baseRec pars cons index args indTyp rcu (def x lsargs) =
  case (primQNameEquality x (quote _≡_)) of λ
   { true →
     do lsargsvis ← (removeHidden lsargs)
        lsargs' ← (map' (λ { (arg i term) →
                                do term' ← (getMapConstructorPathType' baseRec pars cons index args indTyp rcu term)
                                   case term' of λ
                                    { (var x' args') →
                                        do argCons ← (generateRefTerm cons)
                                           args'' ← (pure ((vArg (var x' args') ∷ []) ++L argCons))
                                           pure (arg i (def baseRec args''))
                                      ; term'' → pure (arg i term'')
                                    }
                            }) lsargsvis)
        pure (def (quote _≡_) lsargs')
   ; false →
     do x' ← (getType x)
        case! (getBaseType x') of λ
         { (def xty argL) →
           case (_and_ rcu (primQNameEquality xty indTyp)) of λ
            { true →
              do lsargs' ← (map' (λ { (arg i term) →
                                         do term' ← (getMapConstructorPathType' baseRec pars cons index args indTyp false term)
                                            pure (arg i term') }) lsargs)
                 argCons ← (generateRefTerm cons)
                 args' ← (pure ((vArg (def x lsargs') ∷ []) ++L argCons))
                 pure (def baseRec args')
            ; false →
              do lsargs' ← (map' (λ { (arg i term) →
                                         do term' ← (getMapConstructorPathType' baseRec pars cons index args indTyp rcu term)
                                            pure (arg i term') }) lsargs)
                 pure (def x lsargs')
            }
         ; type → pure (def x lsargs)
         }
   }
getMapConstructorPathType' baseRec pars cons index args indTyp rcu (var ref lsargs) =
  do let pind = (pars ++L index)
         refL = (pind ++L args)
     refL' ← (reverseTC refL)
     x ← (getListElement ref refL')
     case (null lsargs) of λ
      { true → pure (var x [])
      ; false →
        do lsargs' ← (map' (λ { (arg i term) →
                                   do term' ← (getMapConstructorPathType' baseRec pars cons index args indTyp rcu term)
                                      pure (arg i term') }) lsargs)
           pure (var x lsargs')
      }
getMapConstructorPathType' baseRec pars cons index args indTyp rcu x = pure x

getMapConstructorPathType : (baseRec : Name) → (pars : List Nat) → (cons : List Nat) → (index : List Nat) → (indTyp : Name) → (indLength : Nat) → Type → TC Type
getMapConstructorPathType baseRec pars cons index indTyp 0 x = getMapConstructorPathType' baseRec pars cons index [] indTyp true x
getMapConstructorPathType baseRec pars cons index indTyp (suc x) (pi (arg info t1) (abs s t2)) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
         index' = (map (λ z → z + 1) index)
         index'' = (index' ∷L 0)
     ty ← (getMapConstructorPathType baseRec pars' cons' index'' indTyp x t2)
     pure (pi (arg info t1) (abs s ty))
getMapConstructorPathType baseRec pars cons index indTyp x y = pure unknown                                                                            

getPaths : (baseRec : Name) → (CRefBase : Nat) → (pars : List Nat) → (cons : List Nat) → (baseTyp : Name) → (indType : Name) → (paths : List Name) → TC Type
getPaths baseRec CRefBase pars cons baseTyp indTyp [] = pure (var CRefBase [])
getPaths baseRec CRefBase pars cons baseTyp indTyp (x ∷ xs) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
     xs' ← (getPaths baseRec (suc CRefBase) pars' cons' baseTyp indTyp xs)
     ty ← (getType x)
     d ← (getParameters baseTyp)
     ty' ← (rmPars d ty)
     index ← (getIndex' baseTyp)
     x' ← (getMapConstructorPathType baseRec pars cons [] indTyp index ty')
     pure (pi (vArg x') (abs "_" xs'))

getRtypePath : (baseTyp : Name) → (indTyp : Name) → (baseRec : Name) →  (pathList : List Name) → (ref : Nat) → (RTy : Type) → TC Type
getRtypePath baseTyp indTyp baseRec pathList ref (pi (arg (arg-info vis rel) t1) (abs s t2)) =
  do t2' ← (getRtypePath baseTyp indTyp baseRec pathList (suc ref) t2)
     pure (pi (arg (arg-info hidden rel) t1) (abs s t2'))
getRtypePath baseTyp indTyp baseRec pathList ref (agda-sort Level) =
  do cns ← (getConstructors baseTyp)
     ty ← (getConsTypes cns)
     lcons ← (getLength cns)
     refls ← (generateRef (suc (suc ref))) -- +1 for "R" and +1 for "C"
     d ← (getParameters baseTyp)
     pars ← (takeTC d refls)
     consPath ← (generateRef (suc lcons)) -- +1 for "C"
     refls' ← (generateRef ((suc (suc ref)) + lcons)) -- +1 for "R" and +1 for "C"
     parsPath ← (takeTC d refls')
     exp ← (getExpRef baseTyp)
     paths ← (getPaths baseRec lcons parsPath consPath baseTyp indTyp pathList)
     funType ← (getMapConsTypeList' baseTyp zero paths pars exp cns)
     Rty' ← (getType baseTyp)
     ls ← (generateRef ref)
     argInfoL ← (getHidArgs Rty')
     Rargs ← (generateRefTerm' argInfoL ls)
     pure (pi (vArg (def indTyp Rargs)) (abs "R" (pi (vArg (agda-sort (lit 0))) (abs "C3" funType)))) 
getRtypePath baseTyp indType baseRec pathList ref x = pure unknown

{-# TERMINATING #-}
βrecMapPath' : (Rpath : Name) → (RpathRef : Nat) → (indRec : Name) → (pars : List Nat) → (cons : List Nat) → (index : List Nat) →
  (args : List Nat) → (argInfo : List ArgInfo) → (indTyp : Name) → Type → TC Type
βrecMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp (pi (arg info t1) (abs s t2)) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
         index' = (map (λ z → z + 1) index)
         args' = (map (λ z → z + 1) args)
         args'' = (args' ∷L 0)
         argInfo' = (argInf ∷L info)
     t1' ← (βrecMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp t1)
     t2' ← (βrecMapPath' Rpath (suc RpathRef) indRec pars' cons' index' args'' argInfo' indTyp t2)
     pure (pi (hArg t1') (abs s t2'))
βrecMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp (def x lsargs) =
  case (primQNameEquality x (quote _≡_)) of λ
   { true →
     do let cons' = (map (λ z → z + 1) cons) -- +1 for lam "x"
            index' = (map (λ z → z + 1) index) -- +1 for lam "x"
        argCons ← (generateRefTerm cons')
        argPars ← (generateRefTermHid pars)
        argInds ← (generateRefTermHid index)
        argInds' ← (generateRefTermHid index')
        argInfo' ← (getHidArgs' argInf)
        argArgs ← (generateRefTerm' argInfo' args)
        args' ← (pure ((argPars ++L argInds) ++L argArgs))
        argIndRec ← (pure (lam visible (abs "x" (def indRec (vArg (var 0 []) ∷ argCons)))))
        pathTyp ← (pure (def Rpath args'))
        CpathTyp ← (pure (var RpathRef argArgs))
        pure (def (quote _≡_) (vArg (def (quote ap) (vArg argIndRec ∷ vArg pathTyp ∷ [])) ∷ vArg CpathTyp ∷ []))
   ; false → pure unknown
   }
βrecMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp (var ref lsargs) =
  do let pind = (pars ++L index)
         refL = (pind ++L args)
     refL' ← (reverseTC refL)
     x ← (getListElement ref refL')
     case (null lsargs) of λ
      { true → pure (var x [])
      ; false →
        do lsargs' ← (map' (λ { (arg i term) →
                                   do term' ← (βrecMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp term)
                                      pure (arg i term') }) lsargs)
           pure (var x lsargs')
      }
βrecMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp x = pure x

βrecMapPath : (Rpath : Name) → (RpathRef : Nat) → (indRec : Name) → (pars : List Nat) → (cons : List Nat) → (index : List Nat) → (indTyp : Name) → (indLength : Nat) → Type → TC Type
βrecMapPath Rpath RpathRef indRec pars cons index indTyp 0 x = βrecMapPath' Rpath RpathRef indRec pars cons index [] [] indTyp x
βrecMapPath Rpath RpathRef indRec pars cons index indTyp (suc x) (pi (arg info t1) (abs s t2)) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
         index' = (map (λ z → z + 1) index)
         index'' = (index' ∷L 0)
     ty ← (βrecMapPath Rpath (suc RpathRef) indRec pars' cons' index'' indTyp x t2)
     pure (pi (hArg t1) (abs s ty))
βrecMapPath Rpath RpathRef indRec pars cons index indTyp x y = pure unknown


getβrecPaths : (baseRec : Name) → (mapPath : Type) → (pars : List Nat) → (cons : List Nat) → (baseTyp : Name) → (indType : Name) → (paths : List Name) → TC Type
getβrecPaths baseRec mapPath pars cons baseTyp indTyp [] = pure mapPath
getβrecPaths baseRec mapPath pars cons baseTyp indTyp (x ∷ xs) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
     xs' ← (getβrecPaths baseRec mapPath pars' cons' baseTyp indTyp xs)
     ty ← (getType x)
     d ← (getParameters baseTyp)
     ty' ← (rmPars d ty)
     index ← (getIndex' baseTyp)
     x' ← (getMapConstructorPathType baseRec pars cons [] indTyp index ty')
     pure (pi (vArg x') (abs "_" xs'))

getβrecRtypePath : (Rpath : Name) → (baseTyp : Name) → (indTyp : Name) → (pathInd : Nat) → (baseRec : Name) →
  (indexList : List Nat) → (indRec : Name) → (pathList : List Name) → (pars : Nat) → (ref : Nat) → (RTy : Type) → TC Type
getβrecRtypePath Rpath baseTyp indTyp pathInd baseRec indLs indRec pathList 0 ref (pi (arg (arg-info vis rel) t1) (abs s t2)) =
  do t2' ← (getβrecRtypePath Rpath baseTyp indTyp pathInd baseRec indLs indRec pathList 0 (suc ref) t2)
     pure t2'
getβrecRtypePath Rpath baseTyp indTyp pathInd baseRec indLs indRec pathList (suc d) ref (pi (arg (arg-info vis rel) t1) (abs s t2)) =
  do t2' ← (getβrecRtypePath Rpath baseTyp indTyp pathInd baseRec indLs indRec pathList d (suc ref) t2)
     pure (pi (arg (arg-info hidden rel) t1) (abs s t2'))
getβrecRtypePath Rpath baseTyp indTyp pathInd baseRec indLs indRec pathList d ref (agda-sort Level) =
  do cns ← (getConstructors baseTyp)
     ty ← (getConsTypes cns)
     lcons ← (getLength cns)
     refls ← (generateRef (suc ref)) -- +1 for "C"
     d ← (getParameters baseTyp)
     pars ← (takeTC d refls)
     consPath ← (generateRef (suc lcons)) -- +1 for "C"
     lpaths ← (getLength pathList)
     consPath' ← (generateRef ((suc lcons) + lpaths)) -- +1 for "C"
     refls' ← (generateRef ((suc ref) + lcons)) -- +1 for "C"
     parsPath ← (takeTC d refls')
     parsPath' ← (pure (map (λ z → z + lpaths) parsPath))
     index ← (getIndex' baseTyp)
     pathTyp ← (getType Rpath)
     pathTyp' ← (rmPars d pathTyp)
     mapPath ← (βrecMapPath Rpath pathInd indRec parsPath' consPath' [] indTyp index pathTyp') 
     paths ← (getβrecPaths baseRec mapPath parsPath consPath baseTyp indTyp pathList)
     funType ← (getMapConsTypeList' baseTyp zero paths pars indLs cns)
     pure (pi (vArg (agda-sort (lit 0))) (abs "C" funType))
getβrecRtypePath Rpath baseTyp indType pathInd baseRec indLs indRec pathList d ref x = pure unknown


generateβRecHit' : Arg Name → (Rpath : Name) → (pathInd : Nat) → (baseType : Name) → (baseRec : Name) →
  (indexList : List Nat) → (indType : Name) → (indRec : Name) → (points : List Name) → (paths : List Name) → TC ⊤
generateβRecHit' (arg i f) Rpath pathInd baseType baseRec indLs indType indRec points paths = 
  do RTy ← (getType baseType)
     d ← (getParameters baseType)
     funTypePath ← (getβrecRtypePath Rpath baseType indType pathInd baseRec indLs indRec paths d zero RTy)
     (declarePostulate (arg i f) funTypePath)


generateβRecHit'' : List (Arg Name) → (Lpaths : List Name) → (pathInd : Nat) → (baseType : Name) → (baseRec : Name) →
  (indexList : List Nat) → (indType : Name) → (indRec : Name) → (points : List Name) → (paths : List Name) → TC ⊤
generateβRecHit'' (x ∷ xs) (p ∷ ps) (suc pathInd) baseType baseRec indLs indType indRec points paths =
  do (generateβRecHit' x p pathInd baseType baseRec indLs indType indRec points paths)
     (generateβRecHit'' xs ps pathInd baseType baseRec indLs indType indRec points paths)
generateβRecHit'' [] p pathInd baseType baseRec indLs indType indRec points paths = pure tt
generateβRecHit'' n p pathInd baseType baseRec indLs indType indRec points paths = pure tt

generateβRecHit : List (Arg Name) → (baseType : Name) → (baseRec : Name) →
  (indType : Name) → (indRec : Name) → (points : List Name) → (paths : List Name) → TC ⊤
generateβRecHit argD baseType baseRec indType indRec points paths =
  do exp ← (getExpRef baseType)
     argL ← (getLength argD)
     (generateβRecHit'' argD paths argL baseType baseRec exp indType indRec points paths)

generateRecHit : Arg Name → List (Arg Name) → (baseType : Name) → (baseRec : Name) → (indType : Name) → (points : List Name) → (paths : List Name) → TC ⊤
generateRecHit (arg i f) argD baseType baseRec indType points paths =
  do lcons ← getConstructors baseType
     lpoints ← getLength points
     lpaths ← getLength paths
     clauses ← getPathClause lpoints lpaths baseRec
     RTy ← getType baseType
     funTypePath ← getRtypePath baseType indType baseRec paths zero RTy
     declareDef (arg i f) funTypePath
     defineFun f clauses
     generateβRecHit argD baseType baseRec indType f points paths
