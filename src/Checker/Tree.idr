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



-- High level design question - should the functions here all use zero quantity?
-- They are just about specifying typing rules, not actually performing
-- typechecking after all (and `forall` sugar is very convenient...)

data WCtx : Type where

data WTag 
  = TCons | TUnit -- , `(:.): (a, UTup) -> UTup`, `(): Unit` 
  | TBuiltinCons -- `__CONS__: a -> UTup -> UTup`
  | TCon | TFun -- `Con: Ty`, `Fun: Ty`
  | TArg | TRes --`arg: Fun -> Ty`, `res: Fun -> Ty`
  | TMember | TEq | TInst -- `(::)`, `(~)`, `(<=|)`
  | TConjunct -- `(/\): (Co, Co) -> Co`
  | TUnion | TInter -- `(|): (Ty, Ty) -> Ty`, `(&): (Ty, Ty) -> Ty`
  | TUnitTy | TTy | TCo  -- `Unit: Ty`, `Ty: Ty`, `Co: Ty`
  -- instable = inst-able = instance-able
  --          = unstable
  -- I like puns ¯\_(ツ)_/¯
  | TInstable | TOpen | TClosed -- `Instable: Ty`, `TOpen: Ty`, `TClosed: Ty`
  | TPromote | TCoBy -- `('): Any -> Type`, `(<<=): (t: Ty, Co(t)) -> Ty`
  -- All identifiers from the source-program are enumerated and become tagged
  -- `T`s
  | T Nat


mutual
  data WExp : Type where
    Tagged : WTag -> WExp
    -- `TBuiltinCons` is special - it is the only constructor of arity >1
    -- For this reason, it is not directly available in source syntax.
    --
    -- The only other reasonablle alternative I think could work is to have all
    -- operator constructors be of arity two - we need some way to pair up
    -- values.
    --
    -- Debatable whether we should actually have a `WExp` that reduces to
    -- `Tagged TBuiltinCons` as first arg but I'm erring on the side of no. It's
    -- just redundant information and calling `ConsApp` in an interpret function
    -- without any mention of builtin-cons is very obviously a bug.
    ConsApp : WExp -> WUTup -> WExp
    -- Constructor application
    App : (f: WCon) -> (x: WExp) 
        -> {argValid: WDict $ member (arg $ conIsFun f) x} 
        -> WExp
    -- TODO: Upgrade to `LamCase`
    Lam : WTy -> WExp -> WExp

  -- `WTy` is defined independently of `WTypedExp` to make encoding type-in-type
  -- possible
  data WTy : Type where
    IsTy : (e: WExp) -> {auto d: WDict $ member ty e} -> WTy

  WCo : Type
  WCo = WTypedExp co

  WCon : Type
  WCon = WTypedExp con

  WFun : Type
  WFun = WTypedExp fun

  WUTup : Type
  WUTup = WTypedExp utup



  
  data WTypedExp : WTy -> Type where
    Is : forall t. (e: WExp) -> {auto d: WDict $ member t e} -> WTypedExp t

  data WDict : WCo -> Type where
    DConjunct : forall co1, co2. 
                WDict co1 -> WDict co2 -> WDict $ conjunct co1 co2
    DEq : forall e1, e2. WDict $ eq e1 e2
    -- Axioms:
    -- for[a, b](x: a, y: b) { (x, y) :: PairTy(a, b)
    DPairInPairTy : forall a, b, x, y
                  . {auto xInA: WDict $ member a x} 
                  -> {auto yInB: WDict (member b y)} 
                  -> WDict $ member (pairTy a b) (pair x y)
    -- Con <: Fun
    -- TODO: We use the direct forall encoding here because we haven't actually
    -- defined subtyping yet!
    DConSubFun : forall f. {fInCon: WDict $ member con f} 
               -> WDict $ member fun f
    -- `(::) :: Fun`
    DMemberInFun : WDict . member fun $ Tagged TMember
    -- `() :: UTup`
    DUnitInUTup : WDict . member utup $ Tagged TUnit
    -- `Ty :: Ty`
    DTyInTy : WDict . member ty $ Tagged TTy
    -- `Co :: Ty`
    DCoInTy : WDict . member ty $ Tagged TCo
    -- `Fun :: Ty`
    DFunInTy : WDict . member ty $ Tagged TFun
    -- `Con :: Ty`
    DConInTy : WDict . member ty $ Tagged TCon
    -- `for(x: Any, y: UTup) { __CONS__(x)(y) :: UTup }`
    DConsInUTup : forall x, y. WDict . member utup $ ConsApp x y
    -- `(|) :: Con`
    DUnionInCon : WDict . member con $ Tagged TUnion
    DNextLvl : forall c. WDict2 c -> WDict c

  WDict2 : WCo -> Type

  -- Idris2 embedding of WTy2 functions/constructors/etc...
  ty : WTy
  ty = IsTy $ Tagged TTy

  co : WTy
  co = IsTy $ Tagged TCo

  con : WTy
  con = IsTy $ Tagged TCon

  conIsFun : WCon -> WFun
  conIsFun (Is f {d}) = Is f {d=DConSubFun {fInCon=d}}
  
  member : WTy -> WExp -> WCo
  -- member t x = Is {t=co} (App (Is (Tagged TMember)) $ pair (projTy t) x)

  conjunct : WCo -> WCo -> WCo

  union : WTy -> WTy -> WTy
  -- union (IsTy x) (IsTy y) = IsTy (App (Is $ Tagged TUnion) $ pair x y)

  builtinCons : WExp -> WUTup -> WExp
  builtinCons x y = ConsApp x y

  utup : WTy


  unit : WUTup
  unit = Is $ Tagged TUnit

  pair : WExp -> WExp -> WExp
  pair x y = builtinCons x $ Is (builtinCons y unit) {d=DConsInUTup}

  -- A couple possible definitions - first is definitely neater though...
  -- Pair(a, b) 
  --   = [x: a, y: b] '(x :. y :. ()) 
  --   = (p: UTup) <<= { length(i) ~ 2 /\ (p ! 0) :: a /\ (p ! 1) :: b }
  pairTy : WTy -> WTy -> WTy


  eq : WExp -> WExp -> WCo

  proj : forall t. WTypedExp t -> WExp
  proj (Is x) = x

  projTy : WTy -> WExp
  projTy (IsTy x) = x

  fun : WTy
  fun = IsTy $ Tagged TFun

  any : WTy

  -- This not being total will be a pain to fix
  -- To avoid having tons of functions that do `impossible` matches on every
  -- built-in, we really need some more sophisticated why to query types and
  -- dictionaries.
  0 arg : WFun -> WTy
  arg (Is (Tagged TMember) {d=DMemberInFun}) = pairTy any ty
  arg (Is (Tagged TUnion) {d=DConSubFun {f=Tagged TUnion}}) 
    = pairTy ty ty
  arg _ = ?todo2

  -- Function application
  app : (f: WFun) -> (x: WExp) -> {argValid: WDict $ member (arg f) x} -> WExp

  infix 0 $$

  ($$) : (f: WFun) -> (x: WExp) -> {argValid: WDict $ member (arg f) x} -> WExp
  ($$) = app


-- 0 wut : forall x, y. WDict (member (pairTy (IsTy (Tagged TTy)) (IsTy (Tagged TTy))) (ConsApp x (Is (ConsApp y (Is (Tagged TUnit))) {d = DConsInUTup {x=y} {y=Is (Tagged TUnit)}})))
-- wut {x=IsTy _ {d}} = DPairInPairTy {xInA=d}


-- `mutual` blocks in Idris2 have some limitations with regards to how recursive
-- definitions (and type signatures) can get.
-- For example `foo` as defined below does not typecheck if placed in the above
-- mutual block
--
-- > foo : pairTy ty ty = arg (conIsFun (Is (Tagged TUnion)))
-- > foo = Refl
--
-- We therefore must create a new mutual block and use forward declarations
-- whenever stuff gets too recursive
mutual
  -- Some signatures of axioms depend on other axioms
  -- Idris2 does not allow variants to appear in sigatures of later variants of
  -- the same type, so instead we must create a second level-dictionary for
  -- these axioms
  data WDict2_ : WCo -> Type where
    -- `for(x: Ty, y: Ty) { x | y :: Ty }`
    DUnionInTy : forall x, y
              . {xInTy: WDict $ member ty x} -> {yInTy: WDict $ member ty y} 
              -> WDict2_ . member ty $ App (Is $ Tagged TUnion) (pair x y) 
              {argValid = DPairInPairTy {a=ty} {b=ty} {x=x} {y=y}}

  WDict2 = WDict2_