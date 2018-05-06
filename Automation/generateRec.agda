-- {-# OPTIONS --verbose tc.unquote.decl:20 #-}
-- {-# OPTIONS --verbose tc.unquote.def:10 #-}
-- {-# OPTIONS --verbose tc.term.expr.top:5 #-}
-- {-# OPTIONS --verbose tc.sample.debug:20 #-}

open import Agda.Builtin.Reflection
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Data.List
open import Agda.Builtin.Unit
open import Automation.reflectionUtils
open import Automation.generateHit
open import Agda.Builtin.Equality

module Automation.generateRec where


getRecArgs2 : (args : List Nat) → (inds : List Nat) → (irefs : List (List Bool)) → TC (List (Arg Term))
getRecArgs2 args inds irefs = bindTC (dropTC 1 args) -- drop C
                                    (λ args' → bindTC (takeTC 1 args) -- take C
                                    (λ argC → bindTC (generateRefTerm argC)
                                    (λ argC' → bindTC (generateIndexRef inds irefs args')
                                    (λ argsR → returnTC (argC' ++L argsR)))))

generateMapRefRec2 : (f : Nat) → (fargs : List (Arg Term)) → (g : Name) → (args : List Nat) → (inds : List Nat) → (irefs : List (List Bool)) → Nat → TC Term
generateMapRefRec2 f fargs g args inds irefs 0 =  bindTC (generateRefTerm args)
                                                  (λ largs → returnTC (def g (vArg (var f fargs) ∷ largs)))
generateMapRefRec2 f fargs g args inds irefs (suc x) = bindTC (generateMapRefRec2 f fargs g args inds irefs x)
                                                             (λ y → returnTC (lam visible (abs "lx" y)))
                                                             
getTermRec : (g : Name) → (inds : List Nat) → (irefs : List (List Bool)) → (f : Nat) → (ref : Nat) → (args : List Nat) → Type → TC Term
getTermRec g inds irefs f 0 args (def ty y) = bindTC (generateRefTerm args)
                                                     (λ largs → returnTC (def g (vArg (var f []) ∷ largs)))
getTermRec g inds irefs f ref args (def ty y) = bindTC (generateRef ref)
                                            (λ ls → bindTC (generateRefTerm ls)
                                            (λ fargs → bindTC (getLength fargs)
                                            (λ len → bindTC (returnTC (map (λ z → z + len) inds))
                                            (λ inds' → bindTC (returnTC (map (λ z → z + len) args))
                                            (λ args' → bindTC (generateMapRefRec2 (f + len) fargs g args' inds' irefs len)
                                            (λ tm → returnTC tm))))))
getTermRec g inds irefs f ref args (pi (arg info dom) (abs s cdom)) = bindTC (getTermRec g inds irefs f (suc ref) args cdom)
                                                                  (λ cdom' → returnTC cdom')
getTermRec g inds irefs f ref args x = returnTC unknown

getTerm : (R : Name) → (ty : Name) → (inds : List Nat) → (irefs : List (List Bool)) → (cRef : Nat) → (lcarg : List Nat) → (lfarg : List Nat) → (cTy : Type) → TC (List (Arg Term))
getTerm R ty inds irefs cRef lcarg lfarg (def qn ls) = returnTC []
getTerm R ty inds irefs cRef lcarg lfarg (pi (arg info dom) (abs s cdom)) = bindTC (getListElement cRef lcarg)
                                                                        (λ r → bindTC (getTerm R ty inds irefs (suc cRef) lcarg lfarg cdom)
                                                                        (λ cdom' →  bindTC (checkCdmR R dom) λ
                                                                                        { true → bindTC (getTermRec ty inds irefs r zero lfarg dom)
                                                                                                         (λ tm → returnTC (arg info (var r []) ∷ vArg tm ∷ cdom')) ;
                                                                                          false → returnTC (arg info (var r []) ∷ cdom') }))
getTerm R ty inds irefs cRef lcarg lfarg x = returnTC []

getClause' : Nat → Nat → (R : Name) → (ty : Name) → (irefs : List (List Bool)) → (indLs : List Nat) → (lcons : List Name) → TC (List Clause)
getClause' l ref R ty irefs [] [] = returnTC []
getClause' l ref R ty irefs (i ∷ is) (x ∷ xs) = bindTC (getType x)
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
                                       (λ inds → bindTC (getListElement ref lfarg)
                                       (λ Ccon →  bindTC (getClause' l (suc ref) R ty irefs is xs)
                                       (λ xs' → bindTC (getIndexRef R i x)
                                       (λ lb → bindTC (isMemberBool true lb) λ
                                          { true → bindTC (getTerm R ty inds irefs zero lcarg (lenlfarg ∷ lfarg) y')
                                                          (λ ltm → returnTC ((clause (vArg (con x laP) ∷ vArg (var (showNat lenlfarg)) ∷ vars) (var Ccon ltm)) ∷ xs')) ;
                                            false → bindTC (rmIndex i y')
                                                           (λ y'' → bindTC (getTerm R ty inds irefs zero lcarg (lenlfarg ∷ lfarg) y'')
                                                           (λ ltm → returnTC ((clause (vArg (con x laP) ∷ vArg (var (showNat lenlfarg)) ∷ vars) (var Ccon ltm)) ∷ xs'))) } )))))))))))))))))))
getClause' l ref R ty irefs x y = returnTC [] -- Invalid case

getClause : Nat → Nat → (R : Name) → (ty : Name) → (indList : List Nat) → (lcons : List Name) → TC (List Clause)
getClause l ref R ty indList lcons = bindTC (getIndexRefInfo R indList lcons)
                                            (λ lbs → bindTC (getIndex R indList)
                                            (λ indLs → (getClause' l ref R ty lbs indLs lcons)))


{-# TERMINATING #-}
getMapConstructorType : (Cref : Nat) → (pars : List Nat) → (R : Name) → (mapTy : Bool) → Type → TC Type
getMapConstructorType Cref pars R mapTy (pi (arg info t1) (abs s t2)) = bindTC (checkCdm (def R []) t1) λ
                                                                         { true → bindTC (returnTC (map (λ z → z + 2) pars)) -- +1 for Rcons and +1 for Ccons
                                                                                         (λ pars' → bindTC (returnTC (map (λ z → z + 1) pars))
                                                                                         (λ pars'' → bindTC (returnTC (pars' ∷L 1)) -- 1 for Rcons and 0 for Ccons -- ((pars' ∷L 1) ∷L 0))
                                                                                         (λ pars''' → bindTC (getMapConstructorType (suc (suc Cref)) pars''' R mapTy t2)
                                                                                         (λ t2' → bindTC (getMapConstructorType Cref pars R false t1)
                                                                                         (λ t1' → bindTC (getMapConstructorType (suc Cref) pars'' R false t1)
                                                                                         (λ cdom' → bindTC (changeCodomain (suc Cref) cdom')
                                                                                         (λ cdom'' → returnTC (pi (arg info t1') (abs s (pi (arg info cdom'') (abs "Ccons" t2'))))))))))) ;
                                                                           false → bindTC (returnTC (map (λ z → z + 1) pars))
                                                                                          (λ pars' → bindTC (returnTC (pars' ∷L 0))
                                                                                          (λ pars'' → bindTC (getMapConstructorType (suc Cref) pars'' R mapTy t2)
                                                                                          (λ t2' → bindTC (getMapConstructorType Cref pars R false t1)
                                                                                          (λ t1' → returnTC (pi (arg info t1') (abs s t2')))))) }
getMapConstructorType Cref pars R mapTy (def x lsargs) = bindTC (returnTC (_and_ mapTy (primQNameEquality R x))) λ
                                                                   { true → returnTC (var Cref []) ;
                                                                     false → bindTC (returnTC (null lsargs)) λ
                                                                                    { true → returnTC (def x []) ;
                                                                                      false → bindTC (map' (λ { (arg i term) → bindTC (getMapConstructorType Cref pars R mapTy term)
                                                                                                                                       (λ term' → returnTC (arg i term')) }) lsargs)
                                                                                                      (λ lsargs' → returnTC (def x lsargs')) }}
getMapConstructorType Cref pars R mapTy (var ref lsargs) = bindTC (debugPrint "tc.sample.debug" 20 (strErr "issue : printing pars -->" ∷ strErr (showNat ref) ∷ []))
                                                                  (λ _ → bindTC (printList pars)
                                                                  (λ _ → bindTC (reverseTC pars)
                                                                  (λ pars' → bindTC (getListElement ref pars')
                                                                  (λ x → bindTC (returnTC (null lsargs)) λ
                                                                                { true → returnTC (var x []) ;
                                                                                  false → bindTC (map' (λ { (arg i term) → bindTC (getMapConstructorType Cref pars R mapTy term)
                                                                                                                                   (λ term' → returnTC (arg i term')) }) lsargs)
                                                                                                  (λ lsargs' → returnTC (var x lsargs')) }))))
getMapConstructorType Cref pars R mapTy (lam vis (abs s term)) = bindTC (returnTC (map (λ z → z + 1) pars))
                                                                        (λ pars' → bindTC (returnTC (pars' ∷L 0))
                                                                        (λ pars'' → bindTC (getMapConstructorType Cref pars'' R mapTy term)
                                                                        (λ term' → returnTC (lam vis (abs s term')))))                                                                        
getMapConstructorType Cref pars R mapTy (con cn lsargs) = bindTC (returnTC (null lsargs)) λ
                                                                 { true → returnTC (con cn []) ;
                                                                   false → bindTC (map' (λ { (arg i term) → bindTC (getMapConstructorType Cref pars R mapTy term)
                                                                                                                    (λ term' → returnTC (arg i term')) }) lsargs)
                                                                                   (λ lsargs' → returnTC (con cn lsargs')) }
getMapConstructorType Cref pars R mapTy (meta x lsargs) = bindTC (returnTC (null lsargs)) λ
                                                                 { true → returnTC (meta x []) ;
                                                                   false → bindTC (map' (λ { (arg i term) → bindTC (getMapConstructorType Cref pars R mapTy term)
                                                                                                                    (λ term' → returnTC (arg i term')) }) lsargs)
                                                                                   (λ lsargs' → returnTC (meta x lsargs')) }
getMapConstructorType Cref pars R mapTy (pat-lam cs lsargs) = bindTC (returnTC (null lsargs)) λ
                                                                     { true → returnTC (pat-lam cs []) ;
                                                                       false → bindTC (map' (λ { (arg i term) → bindTC (getMapConstructorType Cref pars R mapTy term)
                                                                                                                    (λ term' → returnTC (arg i term')) }) lsargs)
                                                                                   (λ lsargs' → returnTC (pat-lam cs lsargs')) }
getMapConstructorType Cref pars R mapTy x = returnTC x


-- getRefTypes : 

getMapConsTypeList : Name → (Cref : Nat) → (Crefbase : Nat) → (pars : List Nat) → (indexList : List Nat) → (lcons : List Name) → TC Type
getMapConsTypeList R Cref Crefbase pars [] [] = returnTC (var Crefbase [])
getMapConsTypeList R Cref Crefbase pars (i ∷ is) (x ∷ xs) = bindTC (getParameters R)
                                                          (λ d → bindTC (getType x)
                                                          (λ ty → bindTC (rmPars d ty)
                                                          (λ x' → bindTC (returnTC (map (λ z → z + 1) pars))
                                                          (λ pars' → bindTC (getIndexRef R i x)
                                                          (λ lb → bindTC (isMemberBool true lb) λ
                                                            { true → bindTC (getMapConstructorType Cref pars R true x')
                                                                             (λ t → bindTC (getMapConsTypeList R (suc Cref) Crefbase pars' is xs)
                                                                             (λ xt → returnTC (pi (vArg t) (abs "_" xt)))) ;
                                                              false → bindTC (rmIndex i x')
                                                                             (λ x'' → bindTC (getMapConstructorType Cref pars R true x'')
                                                                             (λ t → bindTC (getMapConsTypeList R (suc Cref) Crefbase pars' is xs)
                                                                             (λ xt → returnTC (pi (vArg t) (abs "_" xt))))) })))))
getMapConsTypeList R Cref Crefbase pars x y = returnTC unknown -- Invalid case

getRtype : (R : Name) → (indexList : List Nat) → (ref : Nat) → (RTy : Type) → TC Type
getRtype R indLs ref (pi (arg (arg-info vis rel) t1) (abs s t2)) = bindTC (getRtype R indLs (suc ref) t2)
                                                                   (λ t2' → returnTC (pi (arg (arg-info hidden rel) t1) (abs s t2')))
getRtype R indLs ref (agda-sort Level) = bindTC (getConstructors R)
                                     (λ cns → bindTC (getConsTypes cns)
                                     (λ ty → bindTC (getLength cns)
                                     (λ lcons → bindTC (generateRef (suc (suc ref))) -- +1 for "R" and +1 for "C"
                                     (λ refls → bindTC (getParameters R)
                                     (λ d → bindTC (getType R)
                                     (λ Rty' → bindTC (generateRef ref)
                                     (λ ls → bindTC (getHidArgs Rty')
                                     (λ argInfoL → bindTC (generateRefTerm' argInfoL ls)
                                     (λ Rargs → bindTC (takeTC d refls)
                                     (λ pars → bindTC (getMapConsTypeList R zero lcons pars indLs cns)
                                     (λ funType → returnTC (pi (vArg (def R Rargs)) (abs "R" (pi (vArg (agda-sort (lit 0))) (abs "C" funType)))))))))))))))      
getRtype R indLs ref x = returnTC unknown

generateRec : Arg Name → Name → (indexList : List Nat) → TC ⊤
generateRec (arg i f) t indLs =
  bindTC (getIndex t indLs) λ indLs' →
  bindTC (getConstructors t) λ cns →
  bindTC (getLength cns) λ lcons →
  bindTC (getClause lcons zero t f indLs cns) λ cls →
  bindTC (getType t) λ RTy → 
  bindTC (getRtype t indLs' zero RTy) λ funType →
  bindTC (declareDef (arg i f) funType) λ _ →
  (defineFun f cls)
