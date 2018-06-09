-- {-# OPTIONS --verbose tc.sample.debug:20 #-}

open import Data.List
open import Data.Bool
open import Function hiding (flip)
open import Agda.Builtin.Reflection
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Automation.utils.reflectionUtils
open import Automation.utils.pathUtils
open import Automation.lib.generateRec using (getMapConstructorType)
open import Automation.lib.generateInd
open import Automation.lib.generateHit

module Automation.lib.generateIndHit where

getPathClauseDep' : (lpoints : Nat) → (lpaths : Nat) → (baseTyp : Name) → (baseRec : Name) →
  (indLs : List Nat) → (cns : List Name) → TC (List Clause)
getPathClauseDep' lpoints lpaths baseTyp baseRec [] [] = pure []
getPathClauseDep' lpoints lpaths baseTyp baseRec (i ∷ is) (x ∷ xs) =
  do xs' ← (getPathClauseDep' lpoints lpaths baseTyp baseRec is xs)
     y ← (getType x)
     d ← (getParameters baseTyp)
     y' ← (rmPars d y)
     vars' ← (getClauseVars zero (lpoints + lpaths))
     vars ← (reverseTC vars')
     argInfo ← (getHidArgs y')
     laP ← (consArgs zero argInfo y')
     args ← (generateRef (suc lpoints)) -- +1 for "C"
     args' ← (pure (map (λ z → z + lpaths) args))
     argTerms ← (generateRefTerm args')
     argC ← (getLength laP)
     argCons ← (generateRef argC)
     laP' ← (returnTC (map (λ z → z + (suc (lpoints + lpaths))) argCons))
     reflaP' ← (generateRefTerm' argInfo laP')
     iargs ← (takeTC i reflaP')
     refargs ← (dropTC i reflaP')
     clargsRef ← (generateRef (d + i))
     clargsRef' ← (pure (map (λ z → z + (suc (argC + (lpoints + lpaths)))) clargsRef))
     clargs ← (generateRefTermHid clargsRef')
     clvars ← (getClauseVarsHid zero (d + i))
     pure ((clause (clvars ++L (vArg (con x laP) ∷ vArg (var "C") ∷ vars)) (def baseRec (clargs ++L (vArg (con x refargs) ∷ argTerms)))) ∷ xs')
getPathClauseDep' lpoints lpaths baseTyp baseRec x y = pure [] -- Invalid case

getPathClauseDep : (lpoints : Nat) → (lpaths : Nat) → (baseTyp : Name) → (baseRec : Name) →
  (cns : List Name) → TC (List Clause)
getPathClauseDep lpoints lpaths baseTyp baseRec cns =
  do exp ← (getExpRef baseTyp)
     (getPathClauseDep' lpoints lpaths baseTyp baseRec exp cns)


{-# TERMINATING #-}
getMapConstructorTypeInd2 : (Cref : Nat) → (cName : Name) → (pars : List Nat) → (inds : List Nat) → (args : List Nat) →
  (R : Name) → (mapTy : Bool) → (cty : Type) → (cns : Name) → Type → TC Type
getMapConstructorTypeInd2 Cref cName pars inds args R mapTy ctype cns (pi (arg info t1) (abs s t2)) =
  case! (checkCdm (def R []) t1) of λ
   { true →
     do let pars' = (map (λ z → z + 2) pars) -- +1 for Rcons (t1') and +1 for Ccons (cdom')
            pars'' = ((pars' ∷L 1) ∷L 0) -- 1 for t1' and 0 for cdom'
            pars''' = (map (λ z → z + 1) pars) -- +1 for Rcons (t1')
            inds' = (map (λ z → z + 1) inds) -- +1 for Rcons (t1') and +1 for Ccons (cdom')
            inds'' = (map (λ z → z + 2) inds) -- +1 for Rcons (t1') and +1 for Ccons (cdom')
            args' = (map (λ z → z + 1) args) -- +1 for Rcons (t1') 
            args'' = (args' ∷L 0) -- 0 for Rcons (t1')
            args''' = (map (λ z → z + 1) args'') -- +1 for Ccons (cdom')
        t1'' ← (getMapConstructorType (suc Cref) pars''' R false t1)
        cdom' ← (changeCodomainInd (suc Cref) (inds' ++L args') zero t1'')
        t2' ← (getMapConstructorTypeInd2 (suc (suc Cref)) cName pars'' inds'' args''' R mapTy ctype cns t2)
        t1' ← (getMapConstructorTypeInd2 Cref cName pars inds args R false ctype cns t1)
        pure (pi (arg info t1') (abs s (pi (arg info cdom') (abs "Ccons" t2'))))
     ; false →
       do let pars' = (map (λ z → z + 1) pars) -- +1 for Rcons (t1')
              pars'' = (pars' ∷L 0) -- 0 for Rcons (t1')
              inds' = (map (λ z → z + 1) inds) -- +1 for Rcons (t1')
              args' = (map (λ z → z + 1) args) -- +1 for Rcons (t1')
              args'' = (args' ∷L 0) -- 0 for Rcons (t1')
          t2' ← (getMapConstructorTypeInd2 (suc Cref) cName pars'' inds' args'' R mapTy ctype cns t2)
          t1' ← (getMapConstructorTypeInd2 Cref cName pars inds args R false ctype cns t1)
          pure (pi (arg info t1') (abs s t2'))
     }
getMapConstructorTypeInd2 Cref cName pars inds args R mapTy ctype cns (def x lsargs) =
  case (_and_ mapTy (primQNameEquality R x)) of λ
   { true →
     do args' ← (generateRefTerm args)
        argInfoL ← (getHidArgs ctype)
        cargs ← (generateRefTerm' argInfoL args)
        d ← (getParameters x)
        index ← (dropTC d lsargs)
        index' ← (updateArgs (inds ++L args) index)
        indexH ← (changeVisToHid index')
        pure (var Cref (indexH ++L (vArg (def cName cargs) ∷ [])))
     ; false →
       case (null lsargs) of λ
        { true → pure (def x [])
        ; false →
            do lsargs' ← (map' (λ { (arg i term) →
                                     do term' ← (getMapConstructorTypeInd2 Cref cName pars inds args R mapTy ctype cns term)
                                        pure (arg i term') })
                                lsargs)
               pure (def x lsargs')
        }
     }
getMapConstructorTypeInd2 Cref cName pars inds args R mapTy ctype cns (var ref lsargs) =
  do pars' ← (reverseTC pars)
     x ← (getListElement ref pars')
     case (null lsargs) of λ
      { true → pure (var x [])
      ; false →
         do lsargs' ← (map' (λ { (arg i term) →
                                  do term' ← (getMapConstructorTypeInd2 Cref cName pars inds args R mapTy ctype cns term)
                                     pure (arg i term') })
                             lsargs)
            pure (var x lsargs')
      }
getMapConstructorTypeInd2 Cref cName pars inds args R mapTy ctype cns (lam vis (abs s term)) =
  do let pars' = (map (λ z → z + 1) pars)
         pars'' = (pars' ∷L 0)
     term' ← (getMapConstructorTypeInd2 Cref cName pars'' inds args R mapTy ctype cns term)
     pure (lam vis (abs s term'))                                                                        
getMapConstructorTypeInd2 Cref cName pars inds args R mapTy ctype cns (con cn lsargs) =
  case (null lsargs) of λ
   { true → pure (con cn [])
   ; false →
     do lsargs' ← (map' (λ { (arg i term) →
                                do term' ← (getMapConstructorTypeInd2 Cref cName pars inds args R mapTy ctype cns term)
                                   pure (arg i term') })
                         lsargs)
        pure (con cn lsargs')
   }
getMapConstructorTypeInd2 Cref cName pars inds args R mapTy ctype cns (meta x lsargs) =
  case (null lsargs) of λ
   { true → pure (meta x [])
   ; false →
     do lsargs' ← (map' (λ { (arg i term) →
                                do term' ← (getMapConstructorTypeInd2 Cref cName pars inds args R mapTy ctype cns term)
                                   pure (arg i term') })
                         lsargs)
        pure (meta x lsargs')
   }
getMapConstructorTypeInd2 Cref cName pars inds args R mapTy ctype cns (pat-lam cs lsargs) =
  case (null lsargs) of λ
   { true → pure (pat-lam cs [])
   ; false →
     do lsargs' ← (map' (λ { (arg i term) →
                                do term' ← (getMapConstructorTypeInd2 Cref cName pars inds args R mapTy ctype cns term)
                                   pure (arg i term') })
                         lsargs)
        pure (pat-lam cs lsargs')
   }
getMapConstructorTypeInd2 Cref cName pars inds args R mapTy ctype cns x = pure x

getMapConstructorTypeInd2' : (Cref : Nat) → (cName : Name) → (pars : List Nat) → (index : List Nat) →
  (R : Name) → (cns : Name) → (indLength : Nat) → Type → TC Type
getMapConstructorTypeInd2' Cref cName pars inds R cns 0 x = getMapConstructorTypeInd2 Cref cName pars inds [] R true x cns x 
getMapConstructorTypeInd2' Cref cName pars inds R cns (suc x) (pi (arg info t1) (abs s t2)) =
  do let pars' = (map (λ z → z + 1) pars)
         pars'' = (pars' ∷L 0) -- pars take index as well and will be used as the only list for var reference
         index' = (map (λ z → z + 1) inds)
         index'' = (index' ∷L 0)
     ty ← (getMapConstructorTypeInd2' (suc Cref) cName pars'' index'' R cns x t2)
     pure (pi (arg info t1) (abs s ty))
getMapConstructorTypeInd2' Cref cName pars inds R cns x y = pure unknown                                                                            

getMapConsTypeListInd' : Name → (Cref : Nat) → (paths : Type) → (pars : List Nat) → (indLs : List Nat) →
  (points : List Name) → (lcons : List Name) → TC Type
getMapConsTypeListInd' R Cref paths pars x y [] = pure paths
getMapConsTypeListInd' R Cref paths pars (i ∷ is) (p ∷ ps) (cn ∷ xs) =
  do let pars' = (map (λ z → z + 1) pars)
     d ← (getParameters R)
     x ← (getType cn)
     x' ← (rmPars d x)
     indL ← (getIndex' R)
     t ← (getMapConstructorTypeInd2' Cref p pars [] R cn i x')
     xt ← (getMapConsTypeListInd' R (suc Cref) paths pars' is ps xs)
     pure (pi (vArg t) (abs "_" xt))
getMapConsTypeListInd' R Cref paths pars x y z = pure unknown


{-# TERMINATING #-}
getMapConstructorPathTypeDep' : (baseRec : Name) → (cref : Nat) → (path : Name) → (pars : List Nat) → (cons : List Nat) → (index : List Nat) →
                                (args : List Nat) → (indTyp : Name) → (ctype : Type) → (recurse : Bool) → Type → TC Type
getMapConstructorPathTypeDep' baseRec cref path pars cons index args indTyp ctype rcu (pi (arg info t1) (abs s t2)) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
         index' = (map (λ z → z + 1) index)
         args' = (map (λ z → z + 1) args)
         args'' = (args' ∷L 0)
     t1' ← (getMapConstructorPathTypeDep' baseRec cref path pars cons index args indTyp ctype rcu t1)
     t2' ← (getMapConstructorPathTypeDep' baseRec (suc cref) path pars' cons' index' args'' indTyp ctype rcu t2)
     pure (pi (arg info t1') (abs s t2'))
getMapConstructorPathTypeDep' baseRec cref path pars cons index args indTyp ctype rcu (def x lsargs) =
  case (primQNameEquality x (quote _≡_)) of λ
   { true →
       do lsargsvis ← (removeHidden lsargs)
          lsargs' ← (map' (λ { (arg i term) →
                                  do term' ← (getMapConstructorPathTypeDep' baseRec cref path pars cons index args indTyp ctype rcu term)
                                     case term' of λ
                                      { (var x' args') →
                                          do argCons ← (generateRefTerm cons)
                                             argPars ← (generateRefTermHid pars)
                                             argInds ← (generateRefTermHid index)
                                             args'' ← (returnTC ((vArg (var x' args') ∷ []) ++L argCons))
                                             pure (arg i (def baseRec args''))
                                      ; term'' → pure (arg i term'')
                                      }
                              })
                           lsargsvis)
          args' ← (generateRefTerm args)
          argInfoL ← (getHidArgs ctype)
          cargs ← (generateRefTerm' argInfoL args)
          fstarg ← (takeTC 1 lsargs') -- take the first argument
          fstarg' ← (pure (vArg (def (quote transport) (vArg (var cref []) ∷ vArg (def path cargs) ∷ fstarg)) ∷ [])) -- trans C (p x) ≡ (p y)
          secarg ← (dropTC 1 lsargs')
          pure (def (quote _≡_) (fstarg' ++L secarg))
   ; false →
       do x' ← (getType x)
          case! (getBaseType x') of λ
           { (def xty argL) →
               case (_and_ rcu (primQNameEquality xty indTyp)) of λ
                { true →
                    do lsargs' ← (map' (λ { (arg i term) →
                                               do term' ← (getMapConstructorPathTypeDep' baseRec cref path pars cons index args indTyp ctype false term)
                                                  pure (arg i term') })
                                        lsargs)
                       argCons ← (generateRefTerm cons)
                       argPars ← (generateRefTermHid pars)
                       argInds ← (generateRefTermHid index)
                       args' ← (pure ((vArg (def x lsargs') ∷ []) ++L argCons))
                       pure (def baseRec args')
                ; false →
                    do lsargs' ← (map' (λ { (arg i term) →
                                               do term' ← (getMapConstructorPathTypeDep' baseRec cref path pars cons index args indTyp ctype rcu term)
                                                  pure (arg i term')
                                           }) lsargs)
                       pure (def x lsargs')
                }
                ; type → pure (def x lsargs)
           }
   }
getMapConstructorPathTypeDep' baseRec cref path pars cons index args indTyp ctype rcu (var ref lsargs) =
  do let pind = (pars ++L index)
         refL = (pind ++L args)
     refL' ← (reverseTC refL)
     x ← (getListElement ref refL')
     case (null lsargs) of λ
      { true → pure (var x [])
      ; false →
          do lsargs' ← (map' (λ { (arg i term) →
                                     do term' ← (getMapConstructorPathTypeDep' baseRec cref path pars cons index args indTyp ctype rcu term)
                                        pure (arg i term') }) lsargs)
             pure (var x lsargs')
      }
getMapConstructorPathTypeDep' baseRec cref path pars cons index args indTyp ctype rcu x = pure x

getMapConstructorPathTypeDep : (baseRec : Name) → (cref : Nat) → (path : Name) → (pars : List Nat) → (cons : List Nat) →
  (index : List Nat) → (indTyp : Name) → (indLength : Nat) → Type → TC Type
getMapConstructorPathTypeDep baseRec cref path pars cons index indTyp 0 x = getMapConstructorPathTypeDep' baseRec cref path pars cons index [] indTyp x true x
getMapConstructorPathTypeDep baseRec cref path pars cons index indTyp (suc x) (pi (arg info t1) (abs s t2)) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
         index' = (map (λ z → z + 1) index)
         index'' = (index' ∷L 0)
     ty ← (getMapConstructorPathTypeDep baseRec (suc cref) path pars' cons' index'' indTyp x t2)
     pure (pi (arg info t1) (abs s ty))
getMapConstructorPathTypeDep baseRec cref path pars cons index indTyp x y = pure unknown                                                                            

getPathsDep : (baseRec : Name) → (CRefBase : Nat) → (pars : List Nat) → (cons : List Nat) → (baseTyp : Name) →
  (indType : Name) → (paths : List Name) → TC Type
getPathsDep baseRec CRefBase pars cons baseTyp indTyp [] = pure (var CRefBase (vArg (var (suc CRefBase) []) ∷ []))
getPathsDep baseRec CRefBase pars cons baseTyp indTyp (x ∷ xs) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
     xs' ← (getPathsDep baseRec (suc CRefBase) pars' cons' baseTyp indTyp xs)
     ty ← (getType x)
     d ← (getParameters baseTyp)
     ty' ← (rmPars d ty)
     index ← (getIndex' baseTyp)
     x' ← (getMapConstructorPathTypeDep baseRec CRefBase x pars cons [] indTyp index ty')
     pure (pi (vArg x') (abs "_" xs'))

getRtypePathDep : (baseTyp : Name) → (indTyp : Name) → (baseRec : Name) → (points : List Name) → (pathList : List Name) →
  (ref : Nat) → (RTy : Type) → TC Type
getRtypePathDep baseTyp indTyp baseRec points pathList ref (pi (arg (arg-info vis rel) t1) (abs s t2)) =
  do t2' ← (getRtypePathDep baseTyp indTyp baseRec points pathList (suc ref) t2)
     pure (pi (arg (arg-info hidden rel) t1) (abs s t2'))
getRtypePathDep baseTyp indTyp baseRec points pathList ref (agda-sort Level) =
  do cns ← (getConstructors baseTyp)
     ty ← (getConsTypes cns)
     lcons ← (getLength cns)
     refls ← (generateRef (suc (suc ref))) -- +1 for "R" and +1 for "C"
     refls'' ← (generateRef (suc ref)) -- +1 for "R"
     d ← (getParameters baseTyp)
     pars ← (takeTC d refls)
     pars' ← (takeTC d refls'')
     consPath ← (generateRef (suc lcons)) -- +1 for "C"
     refls' ← (generateRef ((suc (suc ref)) + lcons)) -- +1 for "R" and +1 for "C"
     parsPath ← (takeTC d refls')
     exp ← (getExpRef baseTyp)
     paths ← (getPathsDep baseRec lcons parsPath consPath baseTyp indTyp pathList)
     funType ← (getMapConsTypeListInd' baseTyp zero paths pars exp points cns)
     Rty' ← (getType baseTyp)
     ls ← (generateRef ref)
     argInfoL ← (getHidArgs Rty')
     Rargs ← (generateRefTerm' argInfoL ls)
     CType ← (getCTypeInd indTyp pars' d Rty')
     pure (pi (vArg (def indTyp Rargs)) (abs "R" (pi (vArg CType) (abs "C" funType))))
getRtypePathDep baseTyp indType baseRec points pathList ref x = pure unknown

{-# TERMINATING #-}
βIndMapPath' : (Rpath : Name) → (RpathRef : Nat) → (indRec : Name) → (pars : List Nat) → (cons : List Nat) → (index : List Nat) →
  (args : List Nat) → (argInfo : List ArgInfo) → (indTyp : Name) → Type → TC Type
βIndMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp (pi (arg info t1) (abs s t2)) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
         index' = (map (λ z → z + 1) index)
         args' = (map (λ z → z + 1) args)
         args'' = (args' ∷L 0)
         argInfo' = (argInf ∷L info)
     t1' ← (βIndMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp t1)
     t2' ← (βIndMapPath' Rpath (suc RpathRef) indRec pars' cons' index' args'' argInfo' indTyp t2)
     pure (pi (hArg t1') (abs s t2'))
βIndMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp (def x lsargs) =
  case (primQNameEquality x (quote _≡_)) of λ
   { true →
     do let cons' = (map (λ z → z + 1) cons) -- +1 for lam "x"
        argCons ← (generateRefTerm cons')
        argPars ← (generateRefTermHid pars)
        argInds ← (generateRefTermHid index)
        argInfo' ← (getHidArgs' argInf)
        argArgs ← (generateRefTerm' argInfo' args)
        args' ← (pure ((argPars ++L argInds) ++L argArgs))
        argIndRec ← (pure (lam visible (abs "x" (def indRec (vArg (var 0 []) ∷ argCons)))))
        pathTyp ← (pure (def Rpath args'))
        CpathTyp ← (pure (var RpathRef argArgs))
        pure (def (quote _≡_) (vArg (def (quote apd) (vArg argIndRec ∷ vArg pathTyp ∷ [])) ∷ vArg CpathTyp ∷ []))
   ; false → pure unknown
   }
βIndMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp (var ref lsargs) =
  do let pind = (pars ++L index)
         refL = (pind ++L args)
     refL' ← (reverseTC refL)
     x ← (getListElement ref refL')
     case (null lsargs) of λ
      { true → pure (var x [])
      ; false →
        do lsargs' ← (map' (λ { (arg i term) →
                                  do term' ← (βIndMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp term)
                                     pure (arg i term') }) lsargs)
           pure (var x lsargs')
      }
βIndMapPath' Rpath RpathRef indRec pars cons index args argInf indTyp x = pure x

βIndMapPath : (Rpath : Name) → (RpathRef : Nat) → (indRec : Name) → (pars : List Nat) → (cons : List Nat) →
  (index : List Nat) → (indTyp : Name) → (indLength : Nat) → Type → TC Type
βIndMapPath Rpath RpathRef indRec pars cons index indTyp 0 x = βIndMapPath' Rpath RpathRef indRec pars cons index [] [] indTyp x
βIndMapPath Rpath RpathRef indRec pars cons index indTyp (suc x) (pi (arg info t1) (abs s t2)) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
         index' = (map (λ z → z + 1) index)
         index'' = (index' ∷L 0)
     ty ← (βIndMapPath Rpath (suc RpathRef) indRec pars' cons' index'' indTyp x t2)
     pure (pi (hArg t1) (abs s ty))
βIndMapPath Rpath RpathRef indRec pars cons index indTyp x y = pure unknown


getβIndPaths : (baseRec : Name) → (mapPath : Type) → (ref : Nat) → (pars : List Nat) → (cons : List Nat) →
  (baseTyp : Name) → (indType : Name) → (paths : List Name) → TC Type
getβIndPaths baseRec mapPath ref pars cons baseTyp indTyp [] = pure mapPath
getβIndPaths baseRec mapPath ref pars cons baseTyp indTyp (x ∷ xs) =
  do let cons' = (map (λ z → z + 1) cons)
         pars' = (map (λ z → z + 1) pars)
     xs' ← (getβIndPaths baseRec mapPath (suc ref) pars' cons' baseTyp indTyp xs)
     ty ← (getType x)
     d ← (getParameters baseTyp)
     cns ← (getConstructors baseTyp)
     lcons ← (getLength cns)
     ty' ← (rmPars d ty)
     index ← (getIndex' baseTyp) -- baseRec CRefBase x pars cons [] indTyp index ty')
     x' ← (getMapConstructorPathTypeDep baseRec (lcons + ref) x pars cons [] indTyp index ty') 
     pure (pi (vArg x') (abs "_" xs'))

getβIndRtypePath : (Rpath : Name) → (baseTyp : Name) → (indTyp : Name) → (pathInd : Nat) → (baseRec : Name) →
  (indRec : Name) → (points : List Name) → (pathList : List Name) → (ref : Nat) → (indLs : List Nat) → (RTy : Type) → TC Type
getβIndRtypePath Rpath baseTyp indTyp pathInd baseRec indRec points pathList ref indLs (pi (arg (arg-info vis rel) t1) (abs s t2)) =
  do t2' ← (getβIndRtypePath Rpath baseTyp indTyp pathInd baseRec indRec points pathList (suc ref) indLs t2)
     pure (pi (arg (arg-info hidden rel) t1) (abs s t2'))
getβIndRtypePath Rpath baseTyp indTyp pathInd baseRec indRec points pathList ref indLs (agda-sort Level) =
  do cns ← (getConstructors baseTyp)
     ty ← (getConsTypes cns)
     lcons ← (getLength cns)
     refls ← (generateRef (suc ref)) -- +1 for "C"
     refls' ← (generateRef ref)
     d ← (getParameters baseTyp)
     pars ← (takeTC d refls)
     pars' ← (takeTC d refls')
     consPath ← (generateRef (suc lcons)) -- +1 for "C"
     lpaths ← (getLength pathList)
     consPath' ← (generateRef ((suc lcons) + lpaths)) -- +1 for "C"
     refls' ← (generateRef ((suc ref) + lcons)) -- +1 for "C"
     parsPath ← (takeTC d refls')
     parsPath' ← (pure (map (λ z → z + lpaths) parsPath))
     index ← (getIndex' baseTyp)
     RTyp ← (getType baseTyp)
     pathTyp ← (getType Rpath)
     pathTyp' ← (rmPars d pathTyp)
     mapPath ← (βIndMapPath Rpath pathInd indRec parsPath' consPath' [] indTyp index pathTyp') 
     paths ← (getβIndPaths baseRec mapPath zero parsPath consPath baseTyp indTyp pathList)
     funType ← (getMapConsTypeListInd' baseTyp zero paths pars indLs points cns)
     CType ← (getCTypeInd indTyp pars' d RTyp)
     pure (pi (vArg CType) (abs "C" funType))
getβIndRtypePath Rpath baseTyp indType pathInd baseRec indRec points pathList ref indLs x = pure unknown


generateβIndHit' : Arg Name → (Rpath : Name) → (pathInd : Nat) → (baseType : Name) → (baseRec : Name) →
  (indType : Name) → (indRec : Name) → (indLs : List Nat) → (points : List Name) → (paths : List Name) → TC ⊤
generateβIndHit' (arg i f) Rpath pathInd baseType baseRec indType indRec indLs points paths = 
  do RTy ← (getType baseType)
     funTypePath ← (getβIndRtypePath Rpath baseType indType pathInd baseRec indRec points paths zero indLs RTy)
     (declarePostulate (arg i f) funTypePath)


generateβIndHit'' : List (Arg Name) → (Lpaths : List Name) → (pathInd : Nat) → (baseType : Name) → (baseRec : Name) →
  (indType : Name) → (indRec : Name) → (indLs : List Nat) → (points : List Name) → (paths : List Name) → TC ⊤
generateβIndHit'' (x ∷ xs) (p ∷ ps) (suc pathInd) baseType baseRec indType indRec indLs points paths =
  do (generateβIndHit' x p pathInd baseType baseRec indType indRec indLs points paths)
     (generateβIndHit'' xs ps pathInd baseType baseRec indType indRec indLs points paths)
generateβIndHit'' [] p pathInd baseType baseRec indType indRec indLs points paths = pure tt
generateβIndHit'' n p pathInd baseType baseRec indType indRec indLs points paths = pure tt

generateβIndHit : List (Arg Name) → (baseType : Name) → (baseRec : Name) →
  (indType : Name) → (indRec : Name) → (points : List Name) → (paths : List Name) → TC ⊤
generateβIndHit argD baseType baseRec indType indRec points paths =
  do exp ← (getExpRef baseType)
     argL ← (getLength argD) 
     (generateβIndHit'' argD paths argL baseType baseRec indType indRec exp points paths)

generateIndHit : Arg Name → List (Arg Name) → (baseType : Name) → (baseRec : Name) →
  (indType : Name) → (points : List Name) → (paths : List Name) → TC ⊤
generateIndHit (arg i f) argD baseType baseRec indType points paths =
  do lcons ← getConstructors baseType
     lpoints ← getLength points
     lpaths ← getLength paths
     clauses ← getPathClauseDep lpoints lpaths baseType baseRec lcons
     RTy ← getType baseType
     funTypePath ← getRtypePathDep baseType indType baseRec points paths zero RTy
     declareDef (arg i f) funTypePath
     defineFun f clauses
     generateβIndHit argD baseType baseRec indType f points paths
