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
open import Function hiding (flip)

module Automation.generateRec where


getRecArgs2 : (args : List Nat) → (inds : List Nat) → (irefs : List (List Bool)) → TC (List (Arg Term))
getRecArgs2 args inds irefs =
  do args' ← dropTC 1 args -- drop C
     argC ← takeTC 1 args -- take C
     argC' ← generateRefTerm argC
     argsR ← generateIndexRef inds irefs args'
     pure (argC' ++L argsR)

generateMapRefRec2 : (f : Nat) → (fargs : List (Arg Term)) → (g : Name) → (args : List Nat) → (inds : List Nat) → (irefs : List (List Bool)) → Nat → TC Term
generateMapRefRec2 f fargs g args inds irefs 0 =
  do largs ← generateRefTerm args
     pure (def g (vArg (var f fargs) ∷ largs))
generateMapRefRec2 f fargs g args inds irefs (suc x) =
  do y ← generateMapRefRec2 f fargs g args inds irefs x
     pure (lam visible (abs "lx" y))

getTermRec : (g : Name) → (inds : List Nat) → (irefs : List (List Bool)) → (f : Nat) → (ref : Nat) → (args : List Nat) → Type → TC Term
getTermRec g inds irefs f 0 args (def ty y) =
  do largs ← generateRefTerm args
     pure (def g (vArg (var f []) ∷ largs))
getTermRec g inds irefs f ref args (def ty y) =
  do ls ← generateRef ref
     fargs ← generateRefTerm ls
     len ← getLength fargs
     let inds' = map (λ z → z + len) inds
         args' = map (λ z → z + len) args
     generateMapRefRec2 (f + len) fargs g args' inds' irefs len
getTermRec g inds irefs f ref args (pi (arg info dom) (abs s cdom)) =
  getTermRec g inds irefs f (suc ref) args cdom
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
getClause' l ref R ty irefs (i ∷ is) (x ∷ xs) =
  do y ← getType x
     d ← getParameters R
     y' ← rmPars d y
     il ← generateRef i
     argC ← getArgsCount 0 y'
     argC' ← getDiff argC i
     vars' ← getClauseVars zero l
     vars ← reverseTC vars'
     lfargRev ← getRef 0 vars
     lfarg ← reverseTC lfargRev
     lenlfarg ← getLength lfarg
     argInfo ← getHidArgs y'
     laP ← consArgs (suc lenlfarg) argInfo y'
     lcargRev ← getRef (suc lenlfarg) laP
     lcarg ← reverseTC lcargRev
     let inds = map (λ z → z + (argC' + (suc lenlfarg))) il
     Ccon ← getListElement ref lfarg
     xs' ← getClause' l (suc ref) R ty irefs is xs
     lb ← getIndexRef R i x
     case! isMemberBool true lb of λ
      { true →
        do ltm ← getTerm R ty inds irefs zero lcarg (lenlfarg ∷ lfarg) y'
           pure ((clause (vArg (con x laP) ∷ vArg (var (showNat lenlfarg)) ∷ vars) (var Ccon ltm)) ∷ xs')
      ; false →
        do y'' ← rmIndex i y'
           ltm ← getTerm R ty inds irefs zero lcarg (lenlfarg ∷ lfarg) y''
           pure ((clause (vArg (con x laP) ∷ vArg (var (showNat lenlfarg)) ∷ vars) (var Ccon ltm)) ∷ xs')
      }
getClause' l ref R ty irefs x y = returnTC [] -- Invalid case

getClause : Nat → Nat → (R : Name) → (ty : Name) → (indList : List Nat) → (lcons : List Name) → TC (List Clause)
getClause l ref R ty indList lcons =
  do lbs ← getIndexRefInfo R indList lcons
     indLs ← getIndex R indList
     getClause' l ref R ty lbs indLs lcons


{-# TERMINATING #-}
getMapConstructorType : (Cref : Nat) → (pars : List Nat) → (R : Name) → (mapTy : Bool) → Type → TC Type
getMapConstructorType Cref pars R mapTy (pi (arg info t1) (abs s t2)) =
  case! checkCdm (def R []) t1 of λ
   { true →
     do let pars' = map (λ z → z + 2) pars -- +1 for Rcons and +1 for Ccons
            pars'' = map (λ z → z + 1) pars
            pars''' = pars' ∷L 1 -- 1 for Rcons and 0 for Ccons -- ((pars' ∷L 1) ∷L 0))
        t2' ← getMapConstructorType (suc (suc Cref)) pars''' R mapTy t2
        t1' ← getMapConstructorType Cref pars R false t1
        cdom' ← getMapConstructorType (suc Cref) pars'' R false t1
        cdom'' ← changeCodomain (suc Cref) cdom'
        pure (pi (arg info t1') (abs s (pi (arg info cdom'') (abs "Ccons" t2'))))
   ; false →
     do let pars' = map (λ z → z + 1) pars
            pars'' = pars' ∷L 0
        t2' ← getMapConstructorType (suc Cref) pars'' R mapTy t2
        t1' ← getMapConstructorType Cref pars R false t1
        pure (pi (arg info t1') (abs s t2'))
   }
getMapConstructorType Cref pars R mapTy (def x lsargs) =
  case (_and_ mapTy (primQNameEquality R x)) of λ
   { true → returnTC (var Cref [])
   ; false →
     case null lsargs of λ
      { true → returnTC (def x [])
      ; false →
        do lsargs' ←
             map' (λ { (arg i term) →
                       do term' ← getMapConstructorType Cref pars R mapTy term
                          returnTC (arg i term') })
                           lsargs
           returnTC (def x lsargs')
      }
   }
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
  do indLs' ← getIndex t indLs
     cns ← getConstructors t
     lcons ← getLength cns
     cls ← getClause lcons zero t f indLs cns
     RTy ← getType t
     funType ← getRtype t indLs' zero RTy
     declareDef (arg i f) funType
     defineFun f cls
