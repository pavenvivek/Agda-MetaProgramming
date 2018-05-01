-- {-# OPTIONS --verbose tc.unquote.decl:20 #-}
-- {-# OPTIONS --verbose tc.unquote.def:10 #-}
-- {-# OPTIONS --verbose tc.term.expr.top:5 #-}
{-# OPTIONS --verbose tc.sample.debug:20 #-}

open import Agda.Builtin.Reflection
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Data.List
open import Automation.reflectionUtils
open import Automation.pathUtils
open import Automation.generateRecHit hiding (getMapConsTypeList') -- using (getMapConstructorPathType) -- ; getMapConsTypeList')
open import Automation.generateRec -- using (getMapConsTypeList')
open import Automation.generateHit

module Automation.generateBetaRec where

{-# TERMINATING #-}
βrecMapPath' : (Rpath : Name) → (RpathRef : Nat) → (indRec : Name) → (pars : List Nat) → (cons : List Nat) → (index : List Nat) →
              (args : List Nat) → (argInfo : List ArgInfo) → (indTyp : Name) → Type → TC Type
βrecMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp (pi (arg info t1) (abs s t2)) =  bindTC (βrecMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp t1)
                                                                                     (λ t1' → bindTC (returnTC (map (λ z → z + 1) cons))
                                                                                     (λ cons' → bindTC (returnTC (map (λ z → z + 1) pars))
                                                                                     (λ pars' → bindTC (returnTC (map (λ z → z + 1) index))
                                                                                     (λ index' → bindTC (returnTC (map (λ z → z + 1) args))
                                                                                     (λ args' → bindTC (returnTC (args' ∷L 0))
                                                                                     (λ args'' → bindTC (returnTC (argInf ∷L info))
                                                                                     (λ argInfo' → bindTC (βrecMapPath' Rpath (suc RpathRef) indRec pars' cons' index' args'' argInfo' indTyp t2)
                                                                                     (λ t2' → returnTC (pi (hArg t1') (abs s t2'))))))))))
βrecMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp (def x lsargs) = bindTC (returnTC (primQNameEquality x (quote _≡_))) λ
                                           { true →  bindTC (returnTC (map (λ z → z + 1) cons)) -- +1 for lam "x"
                                                            (λ cons' → bindTC (generateRefTerm cons')
                                                            (λ argCons → bindTC (generateRefTermHid pars)
                                                            (λ argPars → bindTC (generateRefTermHid index)
                                                            (λ argInds → bindTC (returnTC (map (λ z → z + 1) index)) -- +1 for lam "x"
                                                            (λ index' → bindTC (generateRefTermHid index')
                                                            (λ argInds' → bindTC (getHidArgs' argInf)
                                                            (λ argInfo' → bindTC (generateRefTerm' argInfo' args)
                                                            (λ argArgs → bindTC (returnTC ((argPars ++L argInds) ++L argArgs))
                                                            (λ args' → bindTC (returnTC (lam visible (abs "x" (def indRec (vArg (var 0 []) ∷ argCons)))))
                                                            (λ argIndRec → bindTC (returnTC (def Rpath args'))
                                                            (λ pathTyp → bindTC (returnTC (var RpathRef argArgs))
                                                            (λ CpathTyp → returnTC (def (quote _≡_) (vArg (def (quote ap) (vArg argIndRec ∷ vArg pathTyp ∷ [])) ∷ vArg CpathTyp ∷ [])))))))))))))) ;
                                             false → returnTC unknown
                                           }
βrecMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp (var ref lsargs) =  bindTC (returnTC (pars ++L index))
                                                                (λ pind → bindTC (returnTC (pind ++L args))
                                                                (λ refL → bindTC (reverseTC refL)
                                                                (λ refL' → bindTC (getListElement ref refL')
                                                                (λ x → bindTC (returnTC (null lsargs)) λ
                                                                          { true → returnTC (var x []) ;
                                                                            false → bindTC (map' (λ { (arg i term) → bindTC (βrecMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp term)
                                                                                                                             (λ term' → returnTC (arg i term')) }) lsargs)
                                                                                               (λ lsargs' → returnTC (var x lsargs')) }))))
βrecMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp x = returnTC x

βrecMapPath : (Rpath : Name) → (RpathRef : Nat) → (indRec : Name) → (pars : List Nat) → (cons : List Nat) → (index : List Nat) → (indTyp : Name) → (indLength : Nat) → Type → TC Type
βrecMapPath Rpath RpathRef indRec pars cons index indTyp 0 x = βrecMapPath' Rpath RpathRef indRec pars cons index [] [] indTyp x
βrecMapPath Rpath RpathRef indRec pars cons index indTyp (suc x) (pi (arg info t1) (abs s t2)) = bindTC (returnTC (map (λ z → z + 1) cons))
                                                                            (λ cons' → bindTC (returnTC (map (λ z → z + 1) pars))
                                                                            (λ pars' → bindTC (returnTC (map (λ z → z + 1) index))
                                                                            (λ index' → bindTC (returnTC (index' ∷L 0))
                                                                            (λ index'' → bindTC (βrecMapPath Rpath (suc RpathRef) indRec pars' cons' index'' indTyp x t2)
                                                                            (λ ty → returnTC (pi (hArg t1) (abs s ty)))))))
βrecMapPath Rpath RpathRef indRec pars cons index indTyp x y = returnTC unknown


getβrecPaths : (baseRec : Name) → (mapPath : Type) → (pars : List Nat) → (cons : List Nat) → (baseTyp : Name) → (indType : Name) → (paths : List Name) → TC Type
getβrecPaths baseRec mapPath pars cons baseTyp indTyp [] = returnTC mapPath
getβrecPaths baseRec mapPath pars cons baseTyp indTyp (x ∷ xs) = bindTC (returnTC (map (λ z → z + 1) cons))
                                                        (λ cons' → bindTC (returnTC (map (λ z → z + 1) pars))
                                                        (λ pars' → bindTC (getβrecPaths baseRec mapPath pars' cons' baseTyp indTyp xs)
                                                        (λ xs' → bindTC (getType x)
                                                        (λ ty → bindTC (getParameters baseTyp)
                                                        (λ d → bindTC (rmPars d ty)
                                                        (λ ty' → bindTC (debugPrint "tc.sample.debug" 10 (strErr "issue : getPaths" ∷ []))
                                                        (λ _ → bindTC (getIndex' baseTyp)
                                                        (λ index → bindTC (getMapConstructorPathType baseRec pars cons [] indTyp index ty')
                                                        (λ x' → returnTC (pi (vArg x') (abs "_" xs')))))))))))

getMapConsTypeList' : Name → (Cref : Nat) → (paths : Type) → (pars : List Nat) → (indexList : List Nat) → (lcons : List Name) → TC Type
getMapConsTypeList' R Cref paths pars i [] = returnTC paths
getMapConsTypeList' R Cref paths pars (i ∷ is) (x ∷ xs) = bindTC (getParameters R)
                                                        (λ d → bindTC (getType x)
                                                        (λ ty → bindTC (rmPars d ty)
                                                        (λ x' → bindTC (returnTC (map (λ z → z + 1) pars))
                                                        (λ pars' → bindTC (getIndexRef R i x)
                                                        (λ lb → bindTC (isMemberBool true lb) λ
                                                            { true → bindTC (getMapConstructorType Cref pars R true x')
                                                                            (λ t → bindTC (getMapConsTypeList' R (suc Cref) paths pars' is xs)
                                                                            (λ xt → returnTC (pi (vArg t) (abs "_" xt)))) ;
                                                              false → bindTC (rmIndex i x')
                                                                            (λ x'' → bindTC (getMapConstructorType Cref pars R true x'')
                                                                            (λ t → bindTC (getMapConsTypeList' R (suc Cref) paths pars' is xs)
                                                                            (λ xt → returnTC (pi (vArg t) (abs "_" xt))))) } )))))
getMapConsTypeList' R Cref paths pars x y = returnTC unknown -- Invalid case

getβrecRtypePath : (Rpath : Name) → (baseTyp : Name) → (indTyp : Name) → (pathInd : Nat) → (baseRec : Name) →
                   (indexList : List Nat) → (indRec : Name) → (pathList : List Name) → (pars : Nat) → (ref : Nat) → (RTy : Type) → TC Type
getβrecRtypePath Rpath baseTyp indTyp pathInd baseRec indLs indRec pathList 0 ref (pi (arg (arg-info vis rel) t1) (abs s t2)) = bindTC (getβrecRtypePath Rpath baseTyp indTyp pathInd baseRec
                                                                                                                                                               indLs indRec pathList 0 (suc ref) t2)
                                                                                                                                             (λ t2' → returnTC t2')
getβrecRtypePath Rpath baseTyp indTyp pathInd baseRec indLs indRec pathList (suc d) ref (pi (arg (arg-info vis rel) t1) (abs s t2)) = bindTC (getβrecRtypePath Rpath baseTyp indTyp pathInd baseRec
                                                                                                                                                               indLs indRec pathList d (suc ref) t2)
                                                                                                                                    (λ t2' → returnTC (pi (arg (arg-info hidden rel) t1) (abs s t2')))
getβrecRtypePath Rpath baseTyp indTyp pathInd baseRec indLs indRec pathList d ref (agda-sort Level) = bindTC (getConstructors baseTyp)
                                                          (λ cns → bindTC (getConsTypes cns)
                                                          (λ ty → bindTC (getLength cns)
                                                          (λ lcons → bindTC (generateRef (suc ref)) -- +1 for "C"
                                                          (λ refls → bindTC (getParameters baseTyp)
                                                          (λ d → bindTC (takeTC d refls)
                                                          (λ pars → bindTC (generateRef (suc lcons)) -- +1 for "C"
                                                          (λ consPath → bindTC (getLength pathList)
                                                          (λ lpaths → bindTC (generateRef ((suc lcons) + lpaths)) -- +1 for "C"
                                                          (λ consPath' → bindTC (generateRef ((suc ref) + lcons)) -- +1 for "C"
                                                          (λ refls' → bindTC (takeTC d refls')
                                                          (λ parsPath → bindTC (returnTC (map (λ z → z + lpaths) parsPath))
                                                          (λ parsPath' → bindTC (getIndex' baseTyp)
                                                          (λ index → bindTC (getType Rpath)
                                                          (λ pathTyp → bindTC (rmPars d pathTyp)
                                                          (λ pathTyp' → bindTC (βrecMapPath Rpath pathInd indRec parsPath' consPath' [] indTyp index pathTyp') 
                                                          (λ mapPath → bindTC (getβrecPaths baseRec mapPath parsPath consPath baseTyp indTyp pathList)
                                                          (λ paths → bindTC (getMapConsTypeList' baseTyp zero paths pars indLs cns)
                                                          (λ funType → returnTC (pi (vArg (agda-sort (lit 0))) (abs "C" funType))))))))))))))))))))
getβrecRtypePath Rpath baseTyp indType pathInd baseRec indLs indRec pathList d ref x = returnTC unknown


generateβRecHit' : Arg Name → (Rpath : Name) → (pathInd : Nat) → (baseType : Name) → (baseRec : Name) →
                   (indexList : List Nat) → (indType : Name) → (indRec : Name) → (points : List Name) → (paths : List Name) → TC ⊤
generateβRecHit' (arg i f) Rpath pathInd baseType baseRec indLs indType indRec points paths = 
  bindTC (getType baseType) λ RTy →
  bindTC (getParameters baseType) λ d →
  bindTC (getβrecRtypePath Rpath baseType indType pathInd baseRec indLs indRec paths d zero RTy) λ funTypePath →
  bindTC (debugPrint "tc.sample.debug" 20 (strErr "issue : generateβRecHit' --> " ∷ termErr funTypePath ∷ [])) λ _ → 

  (declarePostulate (arg i f) funTypePath)


generateβRecHit'' : List (Arg Name) → (Lpaths : List Name) → (pathInd : Nat) → (baseType : Name) → (baseRec : Name) →
                    (indexList : List Nat) → (indType : Name) → (indRec : Name) → (points : List Name) → (paths : List Name) → TC ⊤
generateβRecHit'' (x ∷ xs) (p ∷ ps) (suc pathInd) baseType baseRec indLs indType indRec points paths = bindTC (generateβRecHit' x p pathInd baseType baseRec indLs indType indRec points paths) λ _ →
                                                                                                  (generateβRecHit'' xs ps pathInd baseType baseRec indLs indType indRec points paths)
generateβRecHit'' [] p pathInd baseType baseRec indLs indType indRec points paths = returnTC tt
generateβRecHit'' n p pathInd baseType baseRec indLs indType indRec points paths = returnTC tt

generateβRecHit : List (Arg Name) → (baseType : Name) → (indexList : List Nat) → (baseRec : Name) →
                  (indType : Name) → (indRec : Name) → (points : List Name) → (paths : List Name) → TC ⊤
generateβRecHit argD baseType indLs baseRec indType indRec points paths =
  bindTC (getIndex baseType indLs) λ indLs' →
  bindTC (getLength argD) λ argL →
  (generateβRecHit'' argD paths argL baseType baseRec indLs indType indRec points paths)
