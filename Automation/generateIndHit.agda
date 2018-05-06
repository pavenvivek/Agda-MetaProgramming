-- {-# OPTIONS --verbose tc.unquote.decl:20 #-}
-- {-# OPTIONS --verbose tc.unquote.def:10 #-}
-- {-# OPTIONS --verbose tc.term.expr.top:5 #-}
-- {-# OPTIONS --verbose tc.sample.debug:20 #-}

open import Agda.Builtin.Reflection
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Data.List
open import Data.Bool
open import Automation.reflectionUtils
open import Automation.pathUtils
open import Automation.generateRec using (getMapConstructorType)
open import Automation.generateInd
open import Automation.generateHit

module Automation.generateIndHit where

getPathClauseDep : (lpoints : Nat) → (lpaths : Nat) → (baseTyp : Name) → (baseRec : Name) → (indLs : List Nat) → (cns : List Name) → TC (List Clause)
getPathClauseDep lpoints lpaths baseTyp baseRec [] [] = returnTC []
getPathClauseDep lpoints lpaths baseTyp baseRec (i ∷ is) (x ∷ xs) = bindTC (getPathClauseDep lpoints lpaths baseTyp baseRec is xs)
                     (λ xs' → bindTC (getType x)
                     (λ y → bindTC (getParameters baseTyp)
                     (λ d → bindTC (rmPars d y)
                     (λ y' → bindTC (getClauseVars zero (lpoints + lpaths))
                     (λ vars' → bindTC (reverseTC vars')
                     (λ vars → bindTC (getHidArgs y')
                     (λ argInfo → bindTC (consArgs zero argInfo y')
                     (λ laP → bindTC (generateRef (suc lpoints)) -- +1 for "C"
                     (λ args → bindTC (returnTC (map (λ z → z + lpaths) args))
                     (λ args' → bindTC (generateRefTerm args')
                     (λ argTerms → bindTC (getLength laP)
                     (λ argC → bindTC (generateRef argC)
                     (λ argCons → bindTC (returnTC (map (λ z → z + (suc (lpoints + lpaths))) argCons))
                     (λ laP' → bindTC (generateRefTerm' argInfo laP')
                     (λ reflaP' → bindTC (takeTC i reflaP')
                     (λ iargs → bindTC (dropTC i reflaP')
                     (λ refargs → bindTC (generateRef (d + i))
                     (λ clargsRef → bindTC (returnTC (map (λ z → z + (suc (argC + (lpoints + lpaths)))) clargsRef))
                     (λ clargsRef' → bindTC (generateRefTermHid clargsRef')
                     (λ clargs → bindTC (getClauseVarsHid zero (d + i))
                     (λ clvars → bindTC (quoteTC clargsRef')
                     (λ debug' → returnTC ((clause (clvars ++L (vArg (con x laP) ∷ vArg (var "C") ∷ vars)) (def baseRec (clargs ++L (vArg (con x refargs) ∷ argTerms)))) ∷ xs')))))))))))))))))))))))
getPathClauseDep lpoints lpaths baseTyp baseRec x y = returnTC [] -- Invalid case

{-# TERMINATING #-}
getMapConstructorTypeInd2 : (Cref : Nat) → (cName : Name) → (pars : List Nat) → (inds : List Nat) → (args : List Nat) → (R : Name) → (mapTy : Bool) → (cty : Type) → (cns : Name) → Type → TC Type
getMapConstructorTypeInd2 Cref cName pars inds args R mapTy ctype cns (pi (arg info t1) (abs s t2)) = bindTC (checkCdm (def R []) t1) λ
                                                                         { true → bindTC (returnTC (map (λ z → z + 2) pars)) -- +1 for Rcons (t1') and +1 for Ccons (cdom')
                                                                                         (λ pars' → bindTC (returnTC ((pars' ∷L 1) ∷L 0)) -- 1 for t1' and 0 for cdom'
                                                                                         (λ pars'' → bindTC (returnTC (map (λ z → z + 1) pars)) -- +1 for Rcons (t1')
                                                                                         (λ pars''' → bindTC (returnTC (map (λ z → z + 1) inds)) -- +1 for Rcons (t1') and +1 for Ccons (cdom')
                                                                                         (λ inds' → bindTC (returnTC (map (λ z → z + 2) inds)) -- +1 for Rcons (t1') and +1 for Ccons (cdom')
                                                                                         (λ inds'' → bindTC (returnTC (map (λ z → z + 1) args)) -- +1 for Rcons (t1') 
                                                                                         (λ args' → bindTC (returnTC (args' ∷L 0)) -- 0 for Rcons (t1')
                                                                                         (λ args'' → bindTC (returnTC (map (λ z → z + 1) args'')) -- +1 for Ccons (cdom')
                                                                                         (λ args''' → bindTC (getMapConstructorType (suc Cref) pars''' R false t1)
                                                                                         (λ t1'' → bindTC (changeCodomainInd (suc Cref) (inds' ++L args') zero t1'')
                                                                                         (λ cdom' → bindTC (getMapConstructorTypeInd2 (suc (suc Cref)) cName pars'' inds'' args''' R mapTy ctype cns t2)
                                                                                         (λ t2' → bindTC (getMapConstructorTypeInd2 Cref cName pars inds args R false ctype cns t1)
                                                                                         (λ t1' → returnTC (pi (arg info t1') (abs s (pi (arg info cdom') (abs "Ccons" t2')))))))))))))))) ;
                                                                           false → bindTC (returnTC (map (λ z → z + 1) pars)) -- +1 for Rcons (t1')
                                                                                          (λ pars' → bindTC (returnTC (pars' ∷L 0)) -- 0 for Rcons (t1')
                                                                                          (λ pars'' → bindTC (returnTC (map (λ z → z + 1) inds)) -- +1 for Rcons (t1')
                                                                                          (λ inds' → bindTC (returnTC (map (λ z → z + 1) args)) -- +1 for Rcons (t1')
                                                                                          (λ args' → bindTC (returnTC (args' ∷L 0)) -- 0 for Rcons (t1')
                                                                                          (λ args'' → bindTC (getMapConstructorTypeInd2 (suc Cref) cName pars'' inds' args'' R mapTy ctype cns t2)
                                                                                          (λ t2' → bindTC (getMapConstructorTypeInd2 Cref cName pars inds args R false ctype cns t1)
                                                                                          (λ t1' → returnTC (pi (arg info t1') (abs s t2'))))))))) }
getMapConstructorTypeInd2 Cref cName pars inds args R mapTy ctype cns (def x lsargs) = bindTC (returnTC (_and_ mapTy (primQNameEquality R x))) λ
                                                                   { true → bindTC (generateRefTerm args)
                                                                                    (λ args' → bindTC (getHidArgs ctype)
                                                                                    (λ argInfoL → bindTC (generateRefTerm' argInfoL args)
                                                                                    (λ cargs → bindTC (getParameters x)
                                                                                    (λ d → bindTC (dropTC d lsargs)
                                                                                    (λ index → bindTC (updateArgs (inds ++L args) index)
                                                                                    (λ index' → bindTC (changeVisToHid index')
                                                                                    (λ indexH → bindTC (debugPrint "tc.sample.debug" 12 (strErr "Cref in mapconsInd -----> " ∷ [])) 
                                                                                    (λ _ → bindTC (debugPrint "tc.sample.debug" 12 (termErr (def x []) ∷ [])) 
                                                                                    (λ _ → bindTC (printArgs indexH)
                                                                                    (λ _ → (returnTC (var Cref (indexH ++L (vArg (def cName cargs) ∷ [])))))))))))))) ;
                                                                     false → bindTC (returnTC (null lsargs)) λ
                                                                                    { true → returnTC (def x []) ;
                                                                                      false → bindTC (map' (λ { (arg i term) → bindTC (getMapConstructorTypeInd2 Cref cName pars inds args R
                                                                                                                                                                   mapTy ctype cns term)
                                                                                                                                       (λ term' → returnTC (arg i term')) }) lsargs)
                                                                                                      (λ lsargs' → returnTC (def x lsargs')) }}
getMapConstructorTypeInd2 Cref cName pars inds args R mapTy ctype cns (var ref lsargs) = bindTC (reverseTC pars)
                                                                  (λ pars' → bindTC (getListElement ref pars')
                                                                  (λ x → bindTC (returnTC (null lsargs)) λ
                                                                                { true → returnTC (var x []) ;
                                                                                  false → bindTC (map' (λ { (arg i term) → bindTC (getMapConstructorTypeInd2 Cref cName pars inds args R mapTy
                                                                                                                                                              ctype cns term)
                                                                                                                                   (λ term' → returnTC (arg i term')) }) lsargs)
                                                                                                  (λ lsargs' → returnTC (var x lsargs')) }))
getMapConstructorTypeInd2 Cref cName pars inds args R mapTy ctype cns (lam vis (abs s term)) = bindTC (returnTC (map (λ z → z + 1) pars))
                                                                        (λ pars' → bindTC (returnTC (pars' ∷L 0))
                                                                        (λ pars'' → bindTC (getMapConstructorTypeInd2 Cref cName pars'' inds args R mapTy ctype cns term)
                                                                        (λ term' → returnTC (lam vis (abs s term')))))                                                                        
getMapConstructorTypeInd2 Cref cName pars inds args R mapTy ctype cns (con cn lsargs) = bindTC (returnTC (null lsargs)) λ
                                                                 { true → returnTC (con cn []) ;
                                                                   false → bindTC (map' (λ { (arg i term) → bindTC (getMapConstructorTypeInd2 Cref cName pars inds args R mapTy ctype cns term)
                                                                                                                    (λ term' → returnTC (arg i term')) }) lsargs)
                                                                                   (λ lsargs' → returnTC (con cn lsargs')) }
getMapConstructorTypeInd2 Cref cName pars inds args R mapTy ctype cns (meta x lsargs) = bindTC (returnTC (null lsargs)) λ
                                                                 { true → returnTC (meta x []) ;
                                                                   false → bindTC (map' (λ { (arg i term) → bindTC (getMapConstructorTypeInd2 Cref cName pars inds args R mapTy ctype cns term)
                                                                                                                    (λ term' → returnTC (arg i term')) }) lsargs)
                                                                                   (λ lsargs' → returnTC (meta x lsargs')) }
getMapConstructorTypeInd2 Cref cName pars inds args R mapTy ctype cns (pat-lam cs lsargs) = bindTC (returnTC (null lsargs)) λ
                                                                     { true → returnTC (pat-lam cs []) ;
                                                                       false → bindTC (map' (λ { (arg i term) → bindTC (getMapConstructorTypeInd2 Cref cName pars inds args R mapTy ctype cns term)
                                                                                                                    (λ term' → returnTC (arg i term')) }) lsargs)
                                                                                   (λ lsargs' → returnTC (pat-lam cs lsargs')) }
getMapConstructorTypeInd2 Cref cName pars inds args R mapTy ctype cns x = returnTC x

getMapConstructorTypeInd2' : (Cref : Nat) → (cName : Name) → (pars : List Nat) → (index : List Nat) → (R : Name) → (cns : Name) → (indLength : Nat) → Type → TC Type
getMapConstructorTypeInd2' Cref cName pars inds R cns 0 x = getMapConstructorTypeInd2 Cref cName pars inds [] R true x cns x 
getMapConstructorTypeInd2' Cref cName pars inds R cns (suc x) (pi (arg info t1) (abs s t2)) = bindTC (returnTC (map (λ z → z + 1) pars))
                                                                            (λ pars' → bindTC (returnTC (pars' ∷L 0)) -- pars take index as well and will be used as the only list for var reference
                                                                            (λ pars'' → bindTC (returnTC (map (λ z → z + 1) inds))
                                                                            (λ index' → bindTC (returnTC (index' ∷L 0))
                                                                            (λ index'' → bindTC (getMapConstructorTypeInd2' (suc Cref) cName pars'' index'' R cns x t2)
                                                                            (λ ty → returnTC (pi (arg info t1) (abs s ty)))))))
getMapConstructorTypeInd2' Cref cName pars inds R cns x y = returnTC unknown                                                                            

getMapConsTypeListInd' : Name → (Cref : Nat) → (paths : Type) → (pars : List Nat) → (indLs : List Nat) → (points : List Name) → (lcons : List Name) → TC Type
getMapConsTypeListInd' R Cref paths pars x y [] = returnTC paths
getMapConsTypeListInd' R Cref paths pars (i ∷ is) (p ∷ ps) (cn ∷ xs) = bindTC (getParameters R)
                                                          (λ d → bindTC (getType cn)
                                                          (λ x → bindTC (rmPars d x)
                                                          (λ x' → bindTC (getIndex' R)
                                                          (λ indL → bindTC (getMapConstructorTypeInd2' Cref p pars [] R cn i x')
                                                          (λ t → bindTC (returnTC (map (λ z → z + 1) pars))
                                                          (λ pars' → bindTC (getMapConsTypeListInd' R (suc Cref) paths pars' is ps xs)
                                                          (λ xt → returnTC (pi (vArg t) (abs "_" xt)))))))))
getMapConsTypeListInd' R Cref paths pars x y z = returnTC unknown


{-# TERMINATING #-}
getMapConstructorPathTypeDep' : (baseRec : Name) → (cref : Nat) → (path : Name) → (pars : List Nat) → (cons : List Nat) → (index : List Nat) →
                                (args : List Nat) → (indTyp : Name) → (ctype : Type) → (recurse : Bool) → Type → TC Type
getMapConstructorPathTypeDep' baseRec cref path pars cons index args indTyp ctype rcu (pi (arg info t1) (abs s t2)) =  bindTC (getMapConstructorPathTypeDep' baseRec cref path pars
                                                                                                                                                       cons index args indTyp ctype rcu t1)
                                                                                     (λ t1' → bindTC (returnTC (map (λ z → z + 1) cons))
                                                                                     (λ cons' → bindTC (returnTC (map (λ z → z + 1) pars))
                                                                                     (λ pars' → bindTC (returnTC (map (λ z → z + 1) index))
                                                                                     (λ index' → bindTC (returnTC (map (λ z → z + 1) args))
                                                                                     (λ args' → bindTC (returnTC (args' ∷L 0))
                                                                                     (λ args'' → bindTC (getMapConstructorPathTypeDep' baseRec (suc cref) path pars' cons' index' args''
                                                                                                                                       indTyp ctype rcu t2)
                                                                                     (λ t2' → returnTC (pi (arg info t1') (abs s t2')))))))))
getMapConstructorPathTypeDep' baseRec cref path pars cons index args indTyp ctype rcu (def x lsargs) = bindTC (returnTC (primQNameEquality x (quote _≡_))) λ
                                           { true →  bindTC (removeHidden lsargs)
                                                       (λ lsargsvis → bindTC (map' (λ { (arg i term) → bindTC (getMapConstructorPathTypeDep' baseRec cref path pars cons index args
                                                                                                                                              indTyp ctype rcu term)
                                                                                        (λ term' → bindTC (returnTC term') λ
                                                                                            { (var x' args') → bindTC (generateRefTerm cons)
                                                                                                   (λ argCons → bindTC (generateRefTermHid pars)
                                                                                                   (λ argPars → bindTC (generateRefTermHid index)
                                                                                                   (λ argInds → bindTC (returnTC ((vArg (var x' args') ∷ []) ++L argCons))
                                                                                                   (λ args'' → returnTC (arg i (def baseRec args'')))))) ;
                                                                                              term'' → returnTC (arg i term'') }) }) lsargsvis)
                                                       (λ lsargs' → bindTC (generateRefTerm args)
                                                       (λ args' → bindTC (getHidArgs ctype)
                                                       (λ argInfoL → bindTC (generateRefTerm' argInfoL args)
                                                       (λ cargs → bindTC (takeTC 1 lsargs') -- take the first argument
                                                       (λ fstarg → bindTC (returnTC (vArg (def (quote transport) (vArg (var cref []) ∷ vArg (def path cargs) ∷ fstarg)) ∷ [])) -- trans C (p x) ≡ (p y)
                                                       (λ fstarg' → bindTC (dropTC 1 lsargs')
                                                       (λ secarg → returnTC (def (quote _≡_) (fstarg' ++L secarg)))))))))) ;
                                             false → bindTC (getType x)
                                                     (λ x' → bindTC (getBaseType x') λ
                                                      { (def xty argL) → bindTC (returnTC (_and_ rcu (primQNameEquality xty indTyp))) λ
                                                             { true →  bindTC (map' (λ { (arg i term) → bindTC (getMapConstructorPathTypeDep' baseRec cref path pars cons index args
                                                                                                                                               indTyp ctype false term)
                                                                                         (λ term' → returnTC (arg i term')) }) lsargs)
                                                                                    (λ lsargs' → bindTC (generateRefTerm cons)
                                                                               (λ argCons → bindTC (generateRefTermHid pars)
                                                                               (λ argPars → bindTC (generateRefTermHid index)
                                                                               (λ argInds → bindTC (returnTC ((vArg (def x lsargs') ∷ []) ++L argCons))
                                                                               (λ args' → returnTC (def baseRec args')))))) ;
                                                               false → bindTC (map' (λ { (arg i term) → bindTC (getMapConstructorPathTypeDep' baseRec cref path pars cons index args
                                                                                                                                               indTyp ctype rcu term)
                                                                                         (λ term' → returnTC (arg i term')) }) lsargs)
                                                                              (λ lsargs' → returnTC (def x lsargs')) } ;
                                                        type → returnTC (def x lsargs) })
                                           }
getMapConstructorPathTypeDep' baseRec cref path pars cons index args indTyp ctype rcu (var ref lsargs) =  bindTC (returnTC (pars ++L index))
                                                                (λ pind → bindTC (returnTC (pind ++L args))
                                                                (λ refL → bindTC (reverseTC refL)
                                                                (λ refL' → bindTC (getListElement ref refL')
                                                                (λ x → bindTC (returnTC (null lsargs)) λ
                                                                          { true → returnTC (var x []) ;
                                                                            false → bindTC (map' (λ { (arg i term) → bindTC (getMapConstructorPathTypeDep' baseRec cref path pars
                                                                                                                                                            cons index args indTyp ctype rcu term)
                                                                                                                      (λ term' → returnTC (arg i term')) }) lsargs)
                                                                                               (λ lsargs' → returnTC (var x lsargs')) }))))
getMapConstructorPathTypeDep' baseRec cref path pars cons index args indTyp ctype rcu x = returnTC x

getMapConstructorPathTypeDep : (baseRec : Name) → (cref : Nat) → (path : Name) → (pars : List Nat) → (cons : List Nat) → (index : List Nat) →
                               (indTyp : Name) → (indLength : Nat) → Type → TC Type
getMapConstructorPathTypeDep baseRec cref path pars cons index indTyp 0 x = getMapConstructorPathTypeDep' baseRec cref path pars cons index [] indTyp x true x
getMapConstructorPathTypeDep baseRec cref path pars cons index indTyp (suc x) (pi (arg info t1) (abs s t2)) = bindTC (returnTC (map (λ z → z + 1) cons))
                                                                            (λ cons' → bindTC (returnTC (map (λ z → z + 1) pars))
                                                                            (λ pars' → bindTC (returnTC (map (λ z → z + 1) index))
                                                                            (λ index' → bindTC (returnTC (index' ∷L 0))
                                                                            (λ index'' → bindTC (getMapConstructorPathTypeDep baseRec (suc cref) path pars' cons' index'' indTyp x t2)
                                                                            (λ ty → returnTC (pi (arg info t1) (abs s ty)))))))
getMapConstructorPathTypeDep baseRec cref path pars cons index indTyp x y = returnTC unknown                                                                            

getPathsDep : (baseRec : Name) → (CRefBase : Nat) → (pars : List Nat) → (cons : List Nat) → (baseTyp : Name) → (indType : Name) → (paths : List Name) → TC Type
getPathsDep baseRec CRefBase pars cons baseTyp indTyp [] = returnTC (var CRefBase (vArg (var (suc CRefBase) []) ∷ []))
getPathsDep baseRec CRefBase pars cons baseTyp indTyp (x ∷ xs) = bindTC (returnTC (map (λ z → z + 1) cons))
                                                        (λ cons' → bindTC (returnTC (map (λ z → z + 1) pars))
                                                        (λ pars' → bindTC (getPathsDep baseRec (suc CRefBase) pars' cons' baseTyp indTyp xs)
                                                        (λ xs' → bindTC (getType x)
                                                        (λ ty → bindTC (getParameters baseTyp)
                                                        (λ d → bindTC (rmPars d ty)
                                                        (λ ty' → bindTC (debugPrint "tc.sample.debug" 10 (strErr "issue : getPaths" ∷ []))
                                                        (λ _ → bindTC (getIndex' baseTyp)
                                                        (λ index → bindTC (getMapConstructorPathTypeDep baseRec CRefBase x pars cons [] indTyp index ty')
                                                        (λ x' → returnTC (pi (vArg x') (abs "_" xs')))))))))))

getRtypePathDep : (baseTyp : Name) → (indTyp : Name) → (baseRec : Name) → (points : List Name) → (pathList : List Name) →
                  (ref : Nat) → (indLs : List Nat) → (RTy : Type) → TC Type
getRtypePathDep baseTyp indTyp baseRec points pathList ref indLs (pi (arg (arg-info vis rel) t1) (abs s t2)) = bindTC (getRtypePathDep baseTyp indTyp baseRec points pathList (suc ref) indLs t2)
                                                                                        (λ t2' → returnTC (pi (arg (arg-info hidden rel) t1) (abs s t2')))
getRtypePathDep baseTyp indTyp baseRec points pathList ref indLs (agda-sort Level) = bindTC (getConstructors baseTyp)
                                                          (λ cns → bindTC (getConsTypes cns)
                                                          (λ ty → bindTC (getLength cns)
                                                          (λ lcons → bindTC (generateRef (suc (suc ref))) -- +1 for "R" and +1 for "C"
                                                          (λ refls → bindTC (generateRef (suc ref)) -- +1 for "R"
                                                          (λ refls'' → bindTC (getParameters baseTyp)
                                                          (λ d → bindTC (takeTC d refls)
                                                          (λ pars → bindTC (takeTC d refls'')
                                                          (λ pars' → bindTC (debugPrint "tc.sample.debug" 10 (strErr "issue : getRtypePath" ∷ []))
                                                          (λ _ → bindTC (generateRef (suc lcons)) -- +1 for "C"
                                                          (λ consPath → bindTC (generateRef ((suc (suc ref)) + lcons)) -- +1 for "R" and +1 for "C"
                                                          (λ refls' → bindTC (takeTC d refls')
                                                          (λ parsPath → bindTC (getPathsDep baseRec lcons parsPath consPath baseTyp indTyp pathList)
                                                          (λ paths → bindTC (getMapConsTypeListInd' baseTyp zero paths pars indLs points cns)
                                                          (λ funType → bindTC (getType baseTyp)
                                                          (λ Rty' → bindTC (generateRef ref)
                                                          (λ ls → bindTC (getHidArgs Rty')
                                                          (λ argInfoL → bindTC (generateRefTerm' argInfoL ls)
                                                          (λ Rargs → bindTC (getCTypeInd indTyp pars' d Rty')
                                                          (λ CType → returnTC (pi (vArg (def indTyp Rargs)) (abs "R" (pi (vArg CType) (abs "C" funType)))))))))))))))))))))))
getRtypePathDep baseTyp indType baseRec points pathList ref indLs x = returnTC unknown

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

generateIndHit : Arg Name → List (Arg Name) → (baseType : Name) → (indLs : List Nat) → (baseRec : Name) → (indType : Name) → (points : List Name) → (paths : List Name) → TC ⊤
generateIndHit (arg i f) argD baseType indLs baseRec indType points paths =
  bindTC (getIndex baseType indLs) λ indLs' →
  bindTC (getConstructors baseType) λ lcons → 
  bindTC (getLength points) λ lpoints →
  bindTC (getLength paths) λ lpaths →
  bindTC (getPathClauseDep lpoints lpaths baseType baseRec indLs' lcons) λ clause →
  bindTC (getType baseType) λ RTy →
  bindTC (getRtypePathDep baseType indType baseRec points paths zero indLs' RTy) λ funTypePath →
  bindTC (declareDef (arg i f) funTypePath) λ _ →
  bindTC (defineFun f clause) λ _ →
  (generateβIndHit argD baseType indLs baseRec indType f points paths)
