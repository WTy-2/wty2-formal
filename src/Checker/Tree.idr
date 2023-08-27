module Checker.Tree

import Data.So

%unbound_implicits off

-- Below is an attempt to formalise WTy2's type system in Idris2
-- It is very much a work-in-progress but Idris2 has proved itself to be a much
-- nicer language for doing this sort of thing than Haskell (GADTs have their
-- limits)

-- We intentionally DO NOT handle scoping rules as the types are already more
-- than complicated enough. We simply assume all names are unique and scoping
-- is correct.

data WCtx : Type where

data WTag 
  = TCons | TUnit -- , `(:.): (a, UTup) -> UTup`, `(): Unit` 
  | TBuiltinCons -- `__CONS__: a -> UTup -> UTup`
  | TCon | TFun | TArg | TRes -- `Con`, `Fun`, `arg`, `res`
  | TMember | TEq | TInst -- `(::)`, `(~)`, `(<=|)`
  | TConjunct -- `(/\)`
  | TUnion | TIntersection -- `(|)`, `(&)`
  | TUnitTy | TTy | TCo  -- `Unit: Ty`, `Ty`, `Co`
  -- instable = inst-able = instance-able
  --          = unstable
  -- I like puns ¯\_(ツ)_/¯
  | TInstable | TOpen | TClosed -- `Instable`
  | T Nat -- All identifiers from the source-program are enumerated and become
          -- `T Nat`s


mutual
  data WExp : Type where
    Tagged : WTag -> WExp
    -- `TBuiltinCons` is special - it is the only constructor of arity >1
    -- For this reason, it is not directly available in source syntax
    -- The only other alternative I think could work is all operator
    -- constructors are arity two - we need some way to pair up values
    ConsApp : WExp -> WExp -> WExp -> WExp
    -- Constructor application
    App : (f: WCon) -> (x: WExp) 
        -> {argValid: WDict $ member (arg $ conIsFun f) x} 
        -> WExp
    -- TODO: Upgrade to `LamCase`
    Lam : WTy -> WExp -> WExp

  data WTy : Type where
    IsTy : (e: WExp) -> {auto d: WDict $ member ty e} -> WTy


  WCo : Type
  WCo = WTypedExp $ co

  WCon : Type
  WCon = WTypedExp $ con

  WFun : Type
  WFun = WTypedExp fun

  data WDict : WCo -> Type where
    DConjunct : forall co1, co2. 
                WDict co1 -> WDict co2 -> WDict $ conjunct co1 co2
    DEq : forall e1, e2. WDict $ eq e1 e2
    -- Axioms:
    -- `(::) :: Fun`
    DMemberFun : WDict . member fun $ Tagged TMember
    -- `() :: UTup`
    DUnitIsUTup : WDict $ member utup unit
    -- `Ty :: Ty`
    DTyInTy : WDict $ member ty (Tagged TTy)
    -- `Co :: Ty`
    DCoInTy : WDict $ member ty (Tagged TCo)
    -- `Fun :: Ty`
    DFunInTy : WDict $ member ty (Tagged TFun)
    -- `Con :: Ty`
    DConInTy : WDict $ member ty $ Tagged TCon

  -- Would obviously like to have `WTypedExp` indexed by `WTy` not `WExp` but
  -- this amount of recursion in definitions in not possible

  data WTypedExp : WTy -> Type where
    Is : forall t. (e: WExp) -> {auto d: WDict $ member t e} -> WTypedExp t

  -- Idris2 embedding of WTy2 lang constructs

  ty : WTy
  ty = IsTy (Tagged TTy)

  co : WTy
  co = IsTy $ Tagged TCo

  con : WTy
  con = IsTy $ Tagged TCon

  conIsFun : WCon -> WFun
  
  member : WTy -> WExp -> WCo
  -- member t x = Is {t=co} (App (Is (Tagged TMember)) $ pair (projTy t) x)

  conjunct : WCo -> WCo -> WCo

  utup : WTy

  unit : WExp

  pair : WExp -> WExp -> WExp

  pairTy : WTy -> WTy -> WTy

  eq : WExp -> WExp -> WCo

  proj : forall t. WTypedExp t -> WExp
  proj (Is x) = x

  projTy : WTy -> WExp
  projTy (IsTy x) = x

  fun : WTy
  fun = IsTy (Tagged TFun) {d=DFunInTy}

  any : WTy

  -- This not being total will be a pain to fix
  -- To avoid having tons of functions that do `impossible` matches on every
  -- built-in, we really need some more sophisticated why to query types and
  -- dictionaries.
  arg : WFun -> WTy
  arg (Is (Tagged TMember) {d=DMemberFun}) = pairTy any ty
  arg _ = ?todo2

  -- Function application
  app : (f: WFun) -> (x: WExp) -> {argValid: WDict $ member (arg f) x} -> WExp

  infix 0 $$

  ($$) : (f: WFun) -> (x: WExp) -> {argValid: WDict $ member (arg f) x} -> WExp
  ($$) = app