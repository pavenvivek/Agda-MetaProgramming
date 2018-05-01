-- {-# OPTIONS --verbose tc.unquote.decl:20 #-}
-- {-# OPTIONS --verbose tc.unquote.def:10 #-}
-- {-# OPTIONS --verbose tc.term.expr.top:5 #-}
{-# OPTIONS --verbose tc.sample.debug:20 #-}

open import CryptDB_HoTT.agda_lib.Utils
open import CryptDB_HoTT.agda_lib.Vector
-- open import CryptDB_HoTT.agda_lib.Equiv

open import CryptDB_HoTT.cryptography.Paillier-Cryptosystem
open import CryptDB_HoTT.cryptography.RSA-Cryptosystem
open import CryptDB_HoTT.cryptography.OPE-Cryptosystem
open import CryptDB_HoTT.cryptography.ElGamal-Cryptosystem
open import CryptDB_HoTT.cryptography.insert-delete-query
open import CryptDB_HoTT.cryptography.increment-path
open import CryptDB_HoTT.cryptography.encrypted-increment

open import Agda.Builtin.Reflection
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Data.List
open import Automation.reflectionUtils
open import Automation.pathUtils
open import Automation.generateIndHit -- using (getMapConstructorPathTypeDep; getMapConsTypeListInd')
open import Automation.generateInd -- using (getCTypeInd)
open import Automation.generateHit

module Automation.generateBetaInd where

{-# TERMINATING #-}
βIndMapPath' : (Rpath : Name) → (RpathRef : Nat) → (indRec : Name) → (pars : List Nat) → (cons : List Nat) → (index : List Nat) →
              (args : List Nat) → (argInfo : List ArgInfo) → (indTyp : Name) → Type → TC Type
βIndMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp (pi (arg info t1) (abs s t2)) =  bindTC (βIndMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp t1)
                                                                                     (λ t1' → bindTC (returnTC (map (λ z → z + 1) cons))
                                                                                     (λ cons' → bindTC (returnTC (map (λ z → z + 1) pars))
                                                                                     (λ pars' → bindTC (returnTC (map (λ z → z + 1) index))
                                                                                     (λ index' → bindTC (returnTC (map (λ z → z + 1) args))
                                                                                     (λ args' → bindTC (returnTC (args' ∷L 0))
                                                                                     (λ args'' → bindTC (returnTC (argInf ∷L info))
                                                                                     (λ argInfo' → bindTC (βIndMapPath' Rpath (suc RpathRef) indRec pars' cons' index' args'' argInfo' indTyp t2)
                                                                                     (λ t2' → returnTC (pi (hArg t1') (abs s t2'))))))))))
βIndMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp (def x lsargs) = bindTC (returnTC (primQNameEquality x (quote _≡_))) λ
                                           { true →  bindTC (returnTC (map (λ z → z + 1) cons)) -- +1 for lam "x"
                                                        (λ cons' → bindTC (generateRefTerm cons')
                                                        (λ argCons → bindTC (generateRefTermHid pars)
                                                        (λ argPars → bindTC (generateRefTermHid index)
                                                        (λ argInds → bindTC (getHidArgs' argInf)
                                                        (λ argInfo' → bindTC (generateRefTerm' argInfo' args)
                                                        (λ argArgs → bindTC (returnTC ((argPars ++L argInds) ++L argArgs))
                                                        (λ args' → bindTC (returnTC (lam visible (abs "x" (def indRec (vArg (var 0 []) ∷ argCons)))))
                                                        (λ argIndRec → bindTC (returnTC (def Rpath args'))
                                                        (λ pathTyp → bindTC (returnTC (var RpathRef argArgs))
                                                        (λ CpathTyp → returnTC (def (quote _≡_) (vArg (def (quote apd) (vArg argIndRec ∷ vArg pathTyp ∷ [])) ∷ vArg CpathTyp ∷ [])))))))))))) ;
                                             false → returnTC unknown
                                           }
βIndMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp (var ref lsargs) =  bindTC (returnTC (pars ++L index))
                                                                (λ pind → bindTC (returnTC (pind ++L args))
                                                                (λ refL → bindTC (reverseTC refL)
                                                                (λ refL' → bindTC (getListElement ref refL')
                                                                (λ x → bindTC (returnTC (null lsargs)) λ
                                                                          { true → returnTC (var x []) ;
                                                                            false → bindTC (map' (λ { (arg i term) → bindTC (βIndMapPath' Rpath RpathRef indRec pars cons
                                                                                                                                               index args argInf indTyp term)
                                                                                                                             (λ term' → returnTC (arg i term')) }) lsargs)
                                                                                               (λ lsargs' → returnTC (var x lsargs')) }))))
βIndMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp x = returnTC x

βIndMapPath : (Rpath : Name) → (RpathRef : Nat) → (indRec : Name) → (pars : List Nat) → (cons : List Nat) → (index : List Nat) → (indTyp : Name) → (indLength : Nat) → Type → TC Type
βIndMapPath Rpath RpathRef indRec pars cons index indTyp 0 x = βIndMapPath' Rpath RpathRef indRec pars cons index [] [] indTyp x
βIndMapPath Rpath RpathRef indRec pars cons index indTyp (suc x) (pi (arg info t1) (abs s t2)) = bindTC (returnTC (map (λ z → z + 1) cons))
                                                                            (λ cons' → bindTC (returnTC (map (λ z → z + 1) pars))
                                                                            (λ pars' → bindTC (returnTC (map (λ z → z + 1) index))
                                                                            (λ index' → bindTC (returnTC (index' ∷L 0))
                                                                            (λ index'' → bindTC (βIndMapPath Rpath (suc RpathRef) indRec pars' cons' index'' indTyp x t2)
                                                                            (λ ty → returnTC (pi (hArg t1) (abs s ty)))))))
βIndMapPath Rpath RpathRef indRec pars cons index indTyp x y = returnTC unknown


getβIndPaths : (baseRec : Name) → (mapPath : Type) → (ref : Nat) → (pars : List Nat) → (cons : List Nat) → (baseTyp : Name) → (indType : Name) → (paths : List Name) → TC Type
getβIndPaths baseRec mapPath ref pars cons baseTyp indTyp [] = returnTC mapPath
getβIndPaths baseRec mapPath ref pars cons baseTyp indTyp (x ∷ xs) = bindTC (returnTC (map (λ z → z + 1) cons))
                                                        (λ cons' → bindTC (returnTC (map (λ z → z + 1) pars))
                                                        (λ pars' → bindTC (getβIndPaths baseRec mapPath (suc ref) pars' cons' baseTyp indTyp xs)
                                                        (λ xs' → bindTC (getType x)
                                                        (λ ty → bindTC (getParameters baseTyp)
                                                        (λ d → bindTC (getConstructors baseTyp)
                                                        (λ cns → bindTC (getLength cns)
                                                        (λ lcons → bindTC (rmPars d ty)
                                                        (λ ty' → bindTC (debugPrint "tc.sample.debug" 10 (strErr "issue : getPaths" ∷ []))
                                                        (λ _ → bindTC (getIndex' baseTyp) -- baseRec CRefBase x pars cons [] indTyp index ty')
                                                        (λ index → bindTC (getMapConstructorPathTypeDep baseRec (lcons + ref) x pars cons [] indTyp index ty') 
                                                        (λ x' → returnTC (pi (vArg x') (abs "_" xs')))))))))))))

getβIndRtypePath : (Rpath : Name) → (baseTyp : Name) → (indTyp : Name) → (pathInd : Nat) → (baseRec : Name) →
                   (indRec : Name) → (points : List Name) → (pathList : List Name) → (ref : Nat) → (indLs : List Nat) → (RTy : Type) → TC Type
getβIndRtypePath Rpath baseTyp indTyp pathInd baseRec indRec points pathList ref indLs (pi (arg (arg-info vis rel) t1) (abs s t2)) = bindTC (getβIndRtypePath Rpath baseTyp indTyp pathInd baseRec
                                                                                                                                                             indRec points pathList (suc ref) indLs t2)
                                                                                        (λ t2' → returnTC (pi (arg (arg-info hidden rel) t1) (abs s t2')))
getβIndRtypePath Rpath baseTyp indTyp pathInd baseRec indRec points pathList ref indLs (agda-sort Level) = bindTC (getConstructors baseTyp)
                                                          (λ cns → bindTC (getConsTypes cns)
                                                          (λ ty → bindTC (getLength cns)
                                                          (λ lcons → bindTC (generateRef (suc ref)) -- +1 for "C"
                                                          (λ refls → bindTC (generateRef ref)
                                                          (λ refls' → bindTC (getParameters baseTyp)
                                                          (λ d → bindTC (takeTC d refls)
                                                          (λ pars → bindTC (takeTC d refls')
                                                          (λ pars' → bindTC (generateRef (suc lcons)) -- +1 for "C"
                                                          (λ consPath → bindTC (getLength pathList)
                                                          (λ lpaths → bindTC (generateRef ((suc lcons) + lpaths)) -- +1 for "C"
                                                          (λ consPath' → bindTC (generateRef ((suc ref) + lcons)) -- +1 for "C"
                                                          (λ refls' → bindTC (takeTC d refls')
                                                          (λ parsPath → bindTC (returnTC (map (λ z → z + lpaths) parsPath))
                                                          (λ parsPath' → bindTC (getIndex' baseTyp)
                                                          (λ index → bindTC (getType baseTyp)
                                                          (λ RTyp → bindTC (getType Rpath)
                                                          (λ pathTyp → bindTC (rmPars d pathTyp)
                                                          (λ pathTyp' → bindTC (βIndMapPath Rpath pathInd indRec parsPath' consPath' [] indTyp index pathTyp') 
                                                          (λ mapPath → bindTC (getβIndPaths baseRec mapPath zero parsPath consPath baseTyp indTyp pathList)
                                                          (λ paths → bindTC (getMapConsTypeListInd' baseTyp zero paths pars indLs points cns)
                                                          (λ funType → bindTC (getCTypeInd indTyp pars' d RTyp)
                                                          (λ CType → returnTC (pi (vArg CType) (abs "C" funType))))))))))))))))))))))))
getβIndRtypePath Rpath baseTyp indType pathInd baseRec indRec points pathList ref indLs x = returnTC unknown


generateβIndHit' : Arg Name → (Rpath : Name) → (pathInd : Nat) → (baseType : Name) → (baseRec : Name) →
                   (indType : Name) → (indRec : Name) → (indLs : List Nat) → (points : List Name) → (paths : List Name) → TC ⊤
generateβIndHit' (arg i f) Rpath pathInd baseType baseRec indType indRec indLs points paths = 
  bindTC (getType baseType) λ RTy →
  bindTC (getβIndRtypePath Rpath baseType indType pathInd baseRec indRec points paths zero indLs RTy) λ funTypePath →
  bindTC (debugPrint "tc.sample.debug" 20 (strErr "issue : generateβIndHit' --> " ∷ termErr funTypePath ∷ [])) λ _ → 
  (declarePostulate (arg i f) funTypePath)


generateβIndHit'' : List (Arg Name) → (Lpaths : List Name) → (pathInd : Nat) → (baseType : Name) → (baseRec : Name) →
                    (indType : Name) → (indRec : Name) → (indLs : List Nat) → (points : List Name) → (paths : List Name) → TC ⊤
generateβIndHit'' (x ∷ xs) (p ∷ ps) (suc pathInd) baseType baseRec indType indRec indLs points paths = bindTC (generateβIndHit' x p pathInd baseType baseRec indType indRec indLs points paths) λ _ →
                                                                                                              (generateβIndHit'' xs ps pathInd baseType baseRec indType indRec indLs points paths)
generateβIndHit'' [] p pathInd baseType baseRec indType indRec indLs points paths = returnTC tt
generateβIndHit'' n p pathInd baseType baseRec indType indRec indLs points paths = returnTC tt

generateβIndHit : List (Arg Name) → (baseType : Name) → (indexList : List Nat) → (baseRec : Name) →
                  (indType : Name) → (indRec : Name) → (points : List Name) → (paths : List Name) → TC ⊤
generateβIndHit argD baseType indLs baseRec indType indRec points paths =
  bindTC (getIndex baseType indLs) λ indLs' →
  bindTC (getLength argD) λ argL → 
  (generateβIndHit'' argD paths argL baseType baseRec indType indRec indLs' points paths)
