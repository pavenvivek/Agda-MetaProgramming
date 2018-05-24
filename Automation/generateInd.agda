-- {-# OPTIONS --verbose tc.unquote.decl:20 #-}
-- {-# OPTIONS --verbose tc.unquote.def:10 #-}
-- {-# OPTIONS --verbose tc.term.expr.top:5 #-}
-- {-# OPTIONS --verbose tc.sample.debug:20 #-}

open import Agda.Builtin.Reflection
open import Agda.Primitive
open import Data.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Unit
open import Automation.reflectionUtils
open import Automation.generateRec using (getMapConstructorType)
open import Automation.generateHit

open import Agda.Builtin.Equality
-- open import CryptDB_HoTT.agda_lib.Utils
-- open import CryptDB_HoTT.agda_lib.Vector

-- open import CryptDB_HoTT.cryptography.Paillier-Cryptosystem
-- open import CryptDB_HoTT.cryptography.RSA-Cryptosystem
-- open import CryptDB_HoTT.cryptography.OPE-Cryptosystem
-- open import CryptDB_HoTT.cryptography.ElGamal-Cryptosystem
-- open import CryptDB_HoTT.cryptography.insert-delete-query
-- open import CryptDB_HoTT.cryptography.increment-path
-- open import CryptDB_HoTT.cryptography.encrypted-increment


module Automation.generateInd where

getTermRecDep : (g : Name) → (ils : List Nat) → (irefs : List (List Bool)) → (f : Nat) → (ref : Nat) → (args : List Nat) → Type → TC Term
getTermRecDep g ils irefs f 0 args (def ty y) = bindTC (generateRefTerm args)
                                          (λ gargs → returnTC (def g (vArg (var f []) ∷ gargs)))
getTermRecDep g ils irefs f ref args (def ty y) = bindTC (generateRef ref)
                                            (λ ls → bindTC (generateRefTerm ls)
                                            (λ fargs → bindTC (getLength fargs)
                                            (λ len → bindTC (returnTC (map (λ z → z + len) args))
                                            (λ gargs' → bindTC (generateRefTerm gargs')
                                            (λ gargs → bindTC (generateMapRef (f + len) fargs g gargs len)
                                            (λ tm → returnTC tm))))))
getTermRecDep g ils irefs f ref args (pi (arg info dom) (abs s cdom)) = bindTC (getTermRecDep g ils irefs f (suc ref) args cdom)
                                                                  (λ cdom' → returnTC cdom')
getTermRecDep g ils irefs f ref args x = returnTC unknown

getTermDep : (R : Name) → (ty : Name) → (ils : List Nat) → (irefs : List (List Bool)) → (cRef : Nat) → (lcarg : List Nat) → (lfarg : List Nat) → (cTy : Type) → TC (List (Arg Term))
getTermDep R ty ils irefs cRef lcarg lfarg (def qn ls) = returnTC []
getTermDep R ty ils irefs cRef lcarg lfarg (pi (arg info dom) (abs s cdom)) = bindTC (getListElement cRef lcarg)
                                                                        (λ r → bindTC (getTermDep R ty ils irefs (suc cRef) lcarg lfarg cdom)
                                                                        (λ cdom' →  bindTC (checkCdmR R dom) λ
                                                                                        { true → bindTC (getTermRecDep ty ils irefs r zero lfarg dom)
                                                                                                         (λ tm → returnTC (arg info (var r []) ∷ vArg tm ∷ cdom')) ;
                                                                                          false → returnTC (arg info (var r []) ∷ cdom') }))
getTermDep R ty ils irefs cRef lcarg lfarg x = returnTC []

getClauseDep' : Nat → Nat → (R : Name) → (ty : Name) → (irefs : List (List Bool)) → (indList : List Nat) → (lcons : List Name) → TC (List Clause)
getClauseDep' l ref R ty irefs [] [] = returnTC []
getClauseDep' l ref R ty irefs (i ∷ is) (x ∷ xs) = bindTC (getType x)
                                       (λ y → bindTC (getParameters R)
                                       (λ d → bindTC (rmPars d y)
                                       (λ y' → bindTC (generateRef i)
                                       (λ il → bindTC (getArgsCount 0 y')
                                       (λ argC → bindTC (getDiff argC i)
                                       (λ argC' → bindTC (getClauseVars zero l)
                                       (λ vars' →  bindTC (reverseTC vars')
                                       (λ vars → bindTC (getRef 0 vars)
                                       (λ lfargRev → bindTC (reverseTC lfargRev)
                                       (λ lfarg → bindTC (getLength lfarg)
                                       (λ lenlfarg → bindTC (getHidArgs y')
                                       (λ argInfo → bindTC (consArgs (suc lenlfarg) argInfo y')
                                       (λ laP → bindTC (getRef (suc lenlfarg) laP)
                                       (λ lcargRev → bindTC (reverseTC lcargRev)
                                       (λ lcarg → bindTC (returnTC (map (λ z → z + (argC' + (suc lenlfarg))) il)) 
                                       (λ il' → bindTC (getTermDep R ty il' irefs zero lcarg (lenlfarg ∷ lfarg) y')
                                       (λ ltm → bindTC (getListElement ref lfarg)
                                       (λ Ccon →  bindTC (getClauseDep' l (suc ref) R ty irefs is xs)
                                       (λ xs' → returnTC ((clause (vArg (con x laP) ∷ vArg (var (showNat lenlfarg)) ∷ vars) (var Ccon ltm)) ∷ xs'))))))))))))))))))))
getClauseDep' l ref R ty irefs x y = returnTC [] -- Invalid case

getClauseDep : Nat → Nat → (R : Name) → (ty : Name) → (indexList : List Nat) → (lcons : List Name) → TC (List Clause)
getClauseDep l ref R ty indList lcons = bindTC (getIndexRefInfo R indList lcons)
                                               (λ lbs → (getClauseDep' l ref R ty lbs indList lcons))

{-# TERMINATING #-}
getMapConstructorTypeInd : (Cref : Nat) → (pars : List Nat) → (inds : List Nat) → (args : List Nat) → (R : Name) → (mapTy : Bool) → (ctype : Type) → (cns : Name) → Type → TC Type
getMapConstructorTypeInd Cref pars inds args R mapTy ctype cns (pi (arg info t1) (abs s t2)) = bindTC (checkCdm (def R []) t1) λ
                                                                         { true → bindTC (returnTC (map (λ z → z + 2) pars)) -- +1 for Rcons (t1') and +1 for Ccons (cdom')
                                                                                         (λ pars' → bindTC (returnTC (pars' ∷L 1)) -- 1 for t1' and 0 for cdom' -- ((pars' ∷L 1) ∷L 0)
                                                                                         (λ pars'' → bindTC (returnTC (map (λ z → z + 1) pars)) -- +1 for Rcons (t1')
                                                                                         (λ pars''' → bindTC (returnTC (map (λ z → z + 1) inds)) -- +1 for Rcons (t1') and +1 for Ccons (cdom')
                                                                                         (λ inds' → bindTC (returnTC (map (λ z → z + 2) inds)) -- +1 for Rcons (t1') and +1 for Ccons (cdom')
                                                                                         (λ inds'' → bindTC (returnTC (map (λ z → z + 1) args)) -- +1 for Rcons (t1') 
                                                                                         (λ args' → bindTC (returnTC (args' ∷L 0)) -- 0 for Rcons (t1')
                                                                                         (λ args'' → bindTC (returnTC (map (λ z → z + 1) args'')) -- +1 for Ccons (cdom')
                                                                                         (λ args''' → bindTC (getMapConstructorType (suc Cref) pars''' R false t1)
                                                                                         (λ t1'' → bindTC (changeCodomainInd (suc Cref) (inds' ++L args') zero t1'')
                                                                                         (λ cdom' → bindTC (getMapConstructorTypeInd (suc (suc Cref)) pars'' inds'' args''' R mapTy ctype cns t2)
                                                                                         (λ t2' → bindTC (getMapConstructorTypeInd Cref pars inds args R false ctype cns t1)
                                                                                         (λ t1' → returnTC (pi (arg info t1') (abs s (pi (arg info cdom') (abs "Ccons" t2')))))))))))))))) ;
                                                                           false → bindTC (returnTC (map (λ z → z + 1) pars)) -- +1 for Rcons (t1')
                                                                                          (λ pars' → bindTC (returnTC (pars' ∷L 0)) -- 0 for Rcons (t1')
                                                                                          (λ pars'' → bindTC (returnTC (map (λ z → z + 1) inds)) -- +1 for Rcons (t1')
                                                                                          (λ inds' → bindTC (returnTC (map (λ z → z + 1) args)) -- +1 for Rcons (t1')
                                                                                          (λ args' → bindTC (returnTC (args' ∷L 0)) -- 0 for Rcons (t1')
                                                                                          (λ args'' → bindTC (getMapConstructorTypeInd (suc Cref) pars'' inds' args'' R mapTy ctype cns t2)
                                                                                          (λ t2' → bindTC (getMapConstructorTypeInd Cref pars inds args R false ctype cns t1)
                                                                                          (λ t1' → returnTC (pi (arg info t1') (abs s t2'))))))))) }
getMapConstructorTypeInd Cref pars inds args R mapTy ctype cns (def x lsargs) = bindTC (returnTC (_and_ mapTy (primQNameEquality R x))) λ
                                                                   { true → bindTC (generateRefTerm args)
                                                                                    (λ args' → bindTC (getHidArgs ctype)
                                                                                    (λ argInfoL → bindTC (generateRefTerm' argInfoL args)
                                                                                    (λ cargs → bindTC (getParameters x)
                                                                                    (λ d → bindTC (dropTC d lsargs)
                                                                                    (λ index → bindTC (updateArgs (inds ++L args) index)
                                                                                    (λ index' → bindTC (changeVisToHid index')
                                                                                    (λ indexH → bindTC (debugPrint "tc.sample.debug" 12 (strErr "Cref in mapconsInd -----> " ∷ [])) 
                                                                                    (λ _ → bindTC (debugPrint "tc.sample.debug" 12 (termErr (def x []) ∷ [])) 
                                                                                    (λ _ → bindTC (printArgs args')
                                                                                    (λ _ → (returnTC (var Cref (indexH ++L (vArg (con cns cargs) ∷ [])))))))))))))) ;
                                                                     false → bindTC (returnTC (null lsargs)) λ
                                                                                    { true → returnTC (def x []) ;
                                                                                      false → bindTC (map' (λ { (arg i term) → bindTC (getMapConstructorTypeInd Cref pars inds args R mapTy ctype
                                                                                                                                                                  cns term)
                                                                                                                                       (λ term' → returnTC (arg i term')) }) lsargs)
                                                                                                      (λ lsargs' → returnTC (def x lsargs')) }}
getMapConstructorTypeInd Cref pars inds args R mapTy ctype cns (var ref lsargs) = bindTC (reverseTC pars)
                                                                  (λ pars' → bindTC (getListElement ref pars')
                                                                  (λ x → bindTC (returnTC (null lsargs)) λ
                                                                                { true → returnTC (var x []) ;
                                                                                  false → bindTC (map' (λ { (arg i term) → bindTC (getMapConstructorTypeInd Cref pars inds args R mapTy ctype cns term)
                                                                                                                                   (λ term' → returnTC (arg i term')) }) lsargs)
                                                                                                  (λ lsargs' → returnTC (var x lsargs')) }))
getMapConstructorTypeInd Cref pars inds args R mapTy ctype cns (lam vis (abs s term)) = bindTC (returnTC (map (λ z → z + 1) pars))
                                                                        (λ pars' → bindTC (returnTC (pars' ∷L 0))
                                                                        (λ pars'' → bindTC (getMapConstructorTypeInd Cref pars'' inds args R mapTy ctype cns term)
                                                                        (λ term' → returnTC (lam vis (abs s term')))))                                                                        
getMapConstructorTypeInd Cref pars inds args R mapTy ctype cns (con cn lsargs) = bindTC (returnTC (null lsargs)) λ
                                                                 { true → returnTC (con cn []) ;
                                                                   false → bindTC (map' (λ { (arg i term) → bindTC (getMapConstructorTypeInd Cref pars inds args R mapTy ctype cns term)
                                                                                                                    (λ term' → returnTC (arg i term')) }) lsargs)
                                                                                   (λ lsargs' → returnTC (con cn lsargs')) }
getMapConstructorTypeInd Cref pars inds args R mapTy ctype cns (meta x lsargs) = bindTC (returnTC (null lsargs)) λ
                                                                 { true → returnTC (meta x []) ;
                                                                   false → bindTC (map' (λ { (arg i term) → bindTC (getMapConstructorTypeInd Cref pars inds args R mapTy ctype cns term)
                                                                                                                    (λ term' → returnTC (arg i term')) }) lsargs)
                                                                                   (λ lsargs' → returnTC (meta x lsargs')) }
getMapConstructorTypeInd Cref pars inds args R mapTy ctype cns (pat-lam cs lsargs) = bindTC (returnTC (null lsargs)) λ
                                                                     { true → returnTC (pat-lam cs []) ;
                                                                       false → bindTC (map' (λ { (arg i term) → bindTC (getMapConstructorTypeInd Cref pars inds args R mapTy ctype cns term)
                                                                                                                    (λ term' → returnTC (arg i term')) }) lsargs)
                                                                                   (λ lsargs' → returnTC (pat-lam cs lsargs')) }
getMapConstructorTypeInd Cref pars inds args R mapTy ctype cns x = returnTC x

getMapConstructorTypeInd' : (Cref : Nat) → (pars : List Nat) → (index : List Nat) → (R : Name) → (cns : Name) → (indLength : Nat) → Type → TC Type
getMapConstructorTypeInd' Cref pars inds R cns 0 x = getMapConstructorTypeInd Cref pars inds [] R true x cns x 
getMapConstructorTypeInd' Cref pars inds R cns (suc x) (pi (arg info t1) (abs s t2)) = bindTC (returnTC (map (λ z → z + 1) pars))
                                                                            (λ pars' → bindTC (returnTC (pars' ∷L 0)) -- pars take index as well and will be used as the only list for var reference
                                                                            (λ pars'' → bindTC (returnTC (map (λ z → z + 1) inds))
                                                                            (λ index' → bindTC (returnTC (index' ∷L 0))
                                                                            (λ index'' → bindTC (getMapConstructorTypeInd' (suc Cref) pars'' index'' R cns x t2)
                                                                            (λ ty → returnTC (pi (arg info t1) (abs s ty)))))))
getMapConstructorTypeInd' Cref pars inds R cns  x y = returnTC unknown                                                                            

getMapConsTypeListInd : Name → (Cref : Nat) → (Crefbase : Nat) → (pars : List Nat) → (indLs : List Nat) → (lcons : List Name) → TC Type
getMapConsTypeListInd R Cref Crefbase pars [] [] = returnTC (var Crefbase (vArg (var (suc Crefbase) []) ∷ []))
getMapConsTypeListInd R Cref Crefbase pars (i ∷ is) (cn ∷ xs) = bindTC (getParameters R)
                                                          (λ d → bindTC (getType cn)
                                                          (λ x → bindTC (rmPars d x)
                                                          (λ x' → bindTC (getMapConstructorTypeInd' Cref pars [] R cn i x')
                                                          (λ t → bindTC (returnTC (map (λ z → z + 1) pars))
                                                          (λ pars' → bindTC (getMapConsTypeListInd R (suc Cref) Crefbase pars' is xs)
                                                          (λ xt → returnTC (pi (vArg t) (abs "_" xt))))))))
getMapConsTypeListInd R Cref Crefbase pars x y = returnTC unknown

getCTypeInd' : (R : Name) → (pars : List Nat) → (indexRef : Nat) → (RTy : Type) → TC Type
getCTypeInd' R pars indexRef (pi (arg (arg-info vis rel) t1) (abs s t2)) = bindTC (returnTC (map (λ z → z + 1) pars))
                                                                         (λ pars' → bindTC (getCTypeInd' R pars' (suc indexRef) t2)
                                                                         (λ t2' → returnTC (pi (arg (arg-info hidden rel) t1) (abs s t2'))))
getCTypeInd' R pars indexRef (agda-sort Level) = bindTC (generateRef indexRef)
                                                   (λ ref' → bindTC (generateRefTerm ref')
                                                   (λ refls → bindTC (generateRefTerm pars)
                                                   (λ pars' → bindTC (getType R)
                                                   (λ Rty → bindTC (getHidPars Rty)
                                                   (λ level → bindTC (dropTC level pars')
                                                   (λ pars'' → bindTC (returnTC (pars'' ++L refls))
                                                   (λ args → returnTC (pi (vArg (def R args)) (abs "RMap" (agda-sort (lit 0)))))))))))
getCTypeInd' R pars indexRef x = returnTC unknown

getCTypeInd : (R : Name) → (pars : List Nat) → (d : Nat) → (RTy : Type) → TC Type
getCTypeInd R pars 0 ty = bindTC (getCTypeInd' R pars zero ty)
                                 (λ ty' → returnTC ty')
getCTypeInd R pars (suc x) (pi (arg info t1) (abs s t2)) = bindTC (getCTypeInd R pars x t2)
                                                                  (λ t2' → returnTC t2')
getCTypeInd R pars x ty = returnTC unknown

getRtypeInd : (R : Name) → (ref : Nat) → (indLs : List Nat) → (RTy : Type) → TC Type
getRtypeInd R ref indLs (pi (arg (arg-info vis rel) t1) (abs s t2)) = bindTC (getRtypeInd R (suc ref) indLs t2)
                                                                   (λ t2' → returnTC (pi (arg (arg-info hidden rel) t1) (abs s t2')))
getRtypeInd R ref indLs (agda-sort Level) = bindTC (getConstructors R)
                                     (λ cns → bindTC (getConsTypes cns)
                                     (λ ty → bindTC (getLength cns)
                                     (λ lcons → bindTC (generateRef (suc (suc ref))) -- +1 for "R" and +1 for "C"
                                     (λ refls → bindTC (generateRef (suc ref)) -- +1 for "R"
                                     (λ refls' → bindTC (getParameters R)
                                     (λ d → bindTC (takeTC d refls)
                                     (λ pars → bindTC (takeTC d refls')
                                     (λ pars' → bindTC (generateRef ref)
                                     (λ ls → bindTC (getMapConsTypeListInd R zero lcons pars indLs cns)
                                     (λ funType → bindTC (getType R)
                                     (λ RType → bindTC (getHidArgs RType)
                                     (λ argInfoL → bindTC (generateRefTerm' argInfoL ls)
                                     (λ Rargs → bindTC (getCTypeInd R pars' d RType)
                                     (λ CType → returnTC (pi (vArg (def R Rargs)) (abs "R" (pi (vArg CType) (abs "C1" funType))))))))))))))))))     
getRtypeInd R ref indLs x = returnTC unknown

generateInd : Arg Name → Name → (indexList : List Nat) → TC ⊤
generateInd (arg i f) t indLs =
  bindTC (getIndex t indLs) λ indLs' →
  bindTC (getConstructors t) λ cns →
  bindTC (getLength cns) λ lcons →
  bindTC (getClauseDep lcons zero t f indLs' cns) λ cls →
  bindTC (getType t) λ RTy →
  bindTC (getRtypeInd t zero indLs' RTy) λ funType → 
  bindTC (declareDef (arg i f) funType) λ _ →
  (defineFun f cls)
