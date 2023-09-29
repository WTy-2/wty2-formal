module Checker.Tree

import Data.So
import Checker.Utils 

-- Not sure what `Prelude.App` does, but name collisions are bad!
%hide Prelude.App

%unbound_implicits off

-- Below is an attempt to formalise WTy2's type system in Idris2
-- It is very much a work-in-progress but Idris2 has proved itself to be a much
-- nicer language for doing this sort of thing than Haskell (GADTs have their
-- limits)


-- High level design question - should the functions here all use zero quantity?
-- They are just about specifying typing rules, not actually performing
-- typechecking after all (and `forall` sugar is very convenient...)

data WCtx : Type where

data WTag 
  = TCons | TUnit -- `(:.): a -> UTup -> UTup`, `(): Unit` 
  | TCon | TFun -- `Con: Ty`, `Fun: Ty`
  | TArg | TRes --`arg: Fun -> Ty`, `res: Fun -> Ty`
  | TMember | TEq -- `(::): Any -> Ty -> Co`, `(~): Any -> Any -> Co`
  | TConjunct -- `(/\): Co -> Co -> Co`
  | TUnion | TInter -- `(|): Ty -> Ty -> Ty`, `(&): Ty -> Ty -> Ty`
  | TUnitTy | TTy | TCo  -- `Unit: Ty`, `Ty: Ty`, `Co: Ty`
  | TAny -- `Any: Ty`
  | TFor -- `for: (t: Ty, t -> Co) -> Co`
  -- instable = inst-able = instance-able
  --          = unstable
  -- I like puns ¯\_(ツ)_/¯
  | TInstable | TOpen | TClosed -- `Instable: Ty`, `TOpen: Ty`, `TClosed: Ty`
  | TPromote | TCoBy -- `('): Any -> Type`, `(<<=): (t: Ty) -> Co(t) -> Ty`
  -- All identifiers from the source-program are enumerated and become tagged
  -- `T`s
  | T Nat


mutual
  data WExp : Type where
    Tagged : WTag -> WExp
    -- Constructor application
    App : (f: WCon) -> WTypedExp (arg $ conIsFun f)
        -- -> {auto argValid: WDict $ member (arg $ conIsFun f) x} 
        -> WExp
    -- TODO: Upgrade to `LamCase`
    -- We need a way of writing patterns (tree of constructors and variables)
    --
    -- This definition obviously breaks with allow shadowing. To ensure
    -- soundness, we would need to write an extrinsic proof that every variable
    -- in checked programs is unique (hopefully not too difficult if we always
    -- generate fresh variables at every binder in the renaming pass)
    Lam : (v: Nat) -> (t: WTy) -> (u: WTy) 
        -> (WDict (member t $ var v) -> WTypedExp u) -> WExp
    Var : Nat -> WExp

  tagged : WTag -> WExp
  tagged = Tagged

  -- `WTy` is defined independently of `WTypedExp` to make encoding type-in-type
  -- possible
  data WTy : Type where
    IsTy : (e: WExp) -> {auto d: WDict $ member ty e} -> WTy

  var : Nat -> WExp
  var = Var

  WCo : Type
  WCo = WTypedExp co

  WCon : Type
  WCon = WTypedExp con

  WFun : Type
  WFun = WTypedExp fun

  WUTup : Type
  WUTup = WTypedExp utup

  WAny : Type
  WAny = WTypedExp any
  
  data WTypedExp : WTy -> Type where
    Is : forall t. (e: WExp) -> {auto d: WDict $ member t e} -> WTypedExp t

  -- We could try and unify `WDict` and `WExp`, thereby defining a core language
  -- where constraints and types are one and the same.
  -- This might become too recursive though (evidence that an expression is a
  -- member of a type is carried with a dictionary, which would then also be
  -- an expression - but then we need a dictionary to carry evidence that that
  -- dictionary is of the correct type etc...)
  data WDict : WCo -> Type where
    DConjunct : forall co1, co2. 
                WDict co1 -> WDict co2 -> WDict $ conjunct co1 co2
    DEq : forall e. WDict $ eq e e

    DInst : forall o, i. {iIsTy: WDict $ member ty i} -> WInstDict o (IsTy i) 
                       -> WDict $ member o i
    -- Axioms:
    -- for[a, b](x: a, y: b) { (x, y) :: PairTy(a, b)
    DPairInPairTy : forall a, b, x, y
                  . {auto xInA: WDict $ member a x} 
                  -> {auto yInB: WDict $ member b y} 
                  -> WDict $ member (pairTy a b) (pair x y)
    -- Con <: Fun
    -- TODO: We use the direct forall encoding here because we haven't actually
    -- defined subtyping yet!
    DConSubFun : forall f. {auto fInCon: WDict $ member con f} 
               -> WDict $ member fun f
    -- `(::) :: Fun`
    DMemberInFun : WDict $ member fun $ Tagged TMember
    -- `() :: UTup`
    DUnitInUTup : WDict $ member utup $ Tagged TUnit
    -- `Ty :: Ty`
    DTyInTy : WDict $ member ty $ Tagged TTy
    -- `Co :: Ty`
    DCoInTy : WDict $ member ty $ Tagged TCo
    -- `Fun :: Ty`
    DFunInTy : WDict $ member ty $ Tagged TFun
    -- `Con :: Ty`
    DConInTy : WDict $ member ty $ Tagged TCon
    -- `Any :: Ty`
    DAnyInTy : WDict $ member ty $ Tagged TAny
    DTySubAny : forall t, x. {auto xInT: WDict $ member t x}
              -> WDict $ member any x
    -- `for(x: Any, y: UTup) { x :> y :: UTup }`
    -- DConsInUTup : forall x, y. WDict . member utup $ ConsApp x y
    -- for(t: Ty, u: Ty, b: t -> u) { { \x: t |-> b(x) } :: Fun }
    DLamInFun : forall v, t, u, b. WDict $ member fun (Lam v t u b)
    -- `(|) :: Con`
    DUnionInCon : WDict $ member con $ Tagged TUnion
    -- `' :: Con`
    DPromoteInCon : WDict $ member con $ Tagged TPromote 
    -- `for(f: Con, x: arg(f)) { f(x) :: res(f) }`
    DAppliedInRes : forall f, x. WDict $ member (res $ conIsFun f) (App f x)
    -- `(:.) :: Con`
    DConsInCon : WDict $ member con $ Tagged TCons
    -- `for(x) { (:.)(x) :: Con }
    DConsedInCon : forall x. WDict $ member con 
                 $ App (Is (Tagged TCons) {d = dConsInCon}) x
    DNextLvl : forall c. WDict2 c -> WDict c

  WDict2 : WCo -> Type

  -- Idris2 embedding of WTy2 functions/constructors/etc...
  ty : WTy
  ty = IsTy $ Tagged TTy

  co : WTy
  co = IsTy $ Tagged TCo

  con : WTy
  con = IsTy $ Tagged TCon

  inter : WTy -> WTy -> WTy

  -- type a ~> b = (f: Con) <<= { a <: arg(f) /\ res(f) <: b }
  conWith : WTy -> WTy -> WTy

  -- type Con2 = (f: Con) <<= { for(x: arg(f)) { f(x) :: Con } }
  --           = [a: Ty, b: Ty, c: Ty] (f: a ~> b ~> c)
  con2 : WTy

  conIsFun : WCon -> WFun
  conIsFun (Is f {d}) = Is f {d=DConSubFun {fInCon=d}}
  
  member : WTy -> WExp -> WCo
  -- member t x = Is {t=co} (App (Is (Tagged TMember)) $ pair (projTy t) x)

  dConsInCon : WDict $ member con $ tagged TCons
  dConsInCon = DConsInCon

  conjunct : WCo -> WCo -> WCo

  union : WTy -> WTy -> WTy

  -- This not being total will be a pain to fix
  -- To avoid having tons of functions that do `impossible` matches on every
  -- axiom dictionary (e.g: `arg (Is _ {d=DTyInTy}) impossible`), we will need 
  -- to restructure somehow.
  0 arg : WFun -> WTy
  arg (Is (Tagged TMember) {d=DMemberInFun}) = pairTy any ty
  arg (Is (Tagged TUnion) {d=DConSubFun {f=Tagged TUnion}}) 
    = pairTy ty ty
  arg (Is (Tagged TPromote)) = any
  arg (Is (Lam _ t _ _)) = t
  -- This case doesn't work because we would need to match every possible
  -- open type `i` to prove it is the same in the instance dict.
  -- There are in theory infinite open types (perhaps when we get down to the
  -- natural case we can use induction/views but that's still a TON of redundant
  -- cases)
  -- Naturally the solution (as always with dependent types) is to model the
  -- data with the datatype - we need dedicated constructors for open types
  -- vs closed ones
  -- This is quite a big refactor, but I think it is sensible
  -- IsOpen would imply that the
  -- arg (Is is_i_I_swear_Idris_pls {d=DInst {o=IsTy {d=DFunInTy} (Tagged TFun)} (InstOf _)}) = ?tmp
  arg _ = ?todo2


  promote : WAny -> WTy
  promote x = IsTy (App (Is $ Tagged TPromote) x) {d = ?huhhhh}


  0 res : WFun -> WTy
  res (Is (Lam _ _ u _)) = u
  res _ = ?todo3
  
  AppCon : (f: WCon) -> (x: WTypedExp $ arg $ conIsFun f) 
        -> WExp
  AppCon = App
  
  -- AppRes : (f: WCon) -> (x: WExp)

  fun : WTy
  fun = IsTy $ Tagged TFun

  isFun : (e: WExp) -> {auto d: WDict $ member fun e} -> WFun
  isCon : (e: WExp) -> {auto d: WDict $ member con e} -> WCon

  IsTyped : forall t. (e: WExp) -> {auto d: WDict $ member t e} -> WTypedExp t
  IsTyped = Is

  -- Apply curried constructor (operator constructor)
  BiApp : (f: WCon) -> (x: WExp) 
        -> { auto xIsArg: WDict $ member (arg $ conIsFun f) x } 
        -> { auto fIsArityTwo: WDict $ member con $ AppCon f (IsTyped x) }
        -> (y: WExp) 
        -> { auto yIsArg: WDict $ member (
          arg $ conIsFun $ isCon $ AppCon f $ IsTyped x
        ) y }
        -> WExp
  -- BiApp f x y = App f x


  -- union (IsTy x) (IsTy y) = IsTy (App (Is $ Tagged TUnion) $ pair x y)

  cons : WExp -> WUTup -> WExp
  cons x y = BiApp (Is (Tagged TCons) {d = ?consIsCon}) x {xIsArg = ?xIsArg} {fIsArityTwo = DConsedInCon} (proj y) {yIsArg = ?yIsArg}

  utup : WTy


  unit : WUTup
  unit = Is $ Tagged TUnit

  pair : WExp -> WExp -> WExp
  pair x y = cons x $ Is (cons y unit) {d = ?todo}

  -- A couple possible definitions - first is definitely neater though...
  -- > Pair(a, b) 
  -- >   = [x: a, y: b] '(x :. y :. ()) 
  -- >   = (p: UTup) <<= { length(i) ~ 2 /\ (p ! 0) :: a /\ (p ! 1) :: b }
  pairTy : WTy -> WTy -> WTy


  eq : WExp -> WExp -> WCo

  -- t <: u = for(x: t) { x :: u }
  sub : WTy -> WTy -> WCo
  

  proj : forall t. WTypedExp t -> WExp
  proj (Is x) = x

  projTy : WTy -> WExp
  projTy (IsTy x) = x

  any : WTy
  any = IsTy $ Tagged TAny

  data WInstDict : WTy -> WTy -> Type where
    InstOf : forall o, i. Tuple (map (\e => WTypedExp $ e i) $ tyMembers o) 
           -> WInstDict o i

  -- Function application
  -- We should be able to match on `f` to find if it is a constructor (in which
  -- case we delegate to `App`) or a lambda (in which case we beta-reduce)
  -- I am currently unsure how to represent such an axiom as "f being a function
  -- means it is either a lambda or a constructor". We might need to model the
  -- data better to achieve this.
  app : (f: WFun) -> (x: WTypedExp $ arg f) -> WTypedExp $ res f

  infix 0 $$

  ($$) : (f: WFun) -> (x: WTypedExp $ arg f) -> WTypedExp $ res f
  ($$) = app

  tyMembers : WTy -> List (WTy -> WTy)
  tyMembers fun = [\_ => ty, \_ => ty] -- arg, res



  toTy : WTypedExp ty -> WTy
  toTy (Is x) = IsTy x

  argAlt : forall fTy. (f: WFun) -> WInstDict fun fTy -> WTy
  argAlt _ (InstOf [x, _]) = toTy x
  argAlt _ _ = ?todo4

  -- Type members can either be defined as taking "self", an object in the type,
  -- or the instance head type itself.
  -- Note the latter only makes sense for open types, but only open types have
  -- members!
  data TyMember : Type where
    SelfTo : WTy -> TyMember
    TyTo : WTy -> TyMember


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
    -- TODO: Work out if this axiom is even necessary - could we just rely on
    -- `res` and the `DAppliedInRes` axiom?
    -- `for(x: Ty, y: Ty) { x | y :: Ty }`
    DUnionedInTy : forall x, y
              . {xInTy: WDict $ member ty x} -> {yInTy: WDict $ member ty y} 
              -> WDict2_ . member ty $ App (Is $ Tagged TUnion) (
                Is (pair x y) {d=DPairInPairTy {a=ty} {b=ty} {x} {y}}
              )
    -- for(x: Any) { 'x :: Ty } 
    DPromotedInTy : forall x. WDict2_ . member ty $ App (Is $ Tagged TPromote) x


  WDict2 = WDict2_
