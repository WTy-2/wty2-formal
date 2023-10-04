{-# OPTIONS --no-positivity-check #-}
-- {-# OPTIONS --lossy-unification #-}

open import Agda.Builtin.Nat
open import Function.Base
open import Data.List.Base
open import Agda.Builtin.Equality

-- Utils

todo : ∀ {a : Set} → a

data Tuple : List Set → Set where
  _∷_ : ∀ {t ts} → (h : t) → (r : Tuple ts) → Tuple (t ∷ ts)
  [] : Tuple []

subst : ∀ {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
subst P refl px = px

-- End Utils

-- I have multiple `postulate`s in the below code that over time should be 
-- removed

data WCtx : Set where

data WTag : Set where
  -- TODO: Define `DepCons` and define ordinary cons in terms of it
  TCons : WTag
  TUnit : WTag
  -- TODO: Define `DepFun` and define 
  -- `Fun = (f: DepFun) <<= { res(f) ~ [t: Ty] const(t) }`
  TFun : WTag
  TArg : WTag
  TRes : WTag
  TMember : WTag
  TEq : WTag
  TConjunct : WTag
  TUnion : WTag
  TInter : WTag
  TCo : WTag
  TAny : WTag
  TFor : WTag
  TOpen : WTag
  TClosed : WTag
  -- TODO: `(')` can be defined in terms of `(~)` and
  -- vice-versa, so we should pick one
  -- `'x = Any <<= { it ~ x }`
  -- `x ~ y = x :: 'y`
  -- The latter appears to be neater, so maybe remove TEq?
  TPromote : WTag
  TSuchThat : WTag
  T : Nat → WTag

data WExp : Set
data WTy : Set
data WTypedExp : WTy -> Set
data WOpen : Set

WCon : Set
WFun : Set
WCo : Set
WUTup : Set
WAny : Set
WClosed : Set

data WDict : WCo -> Set

ty : WOpen
tyInTy : WTy
co : WOpen
fun : WOpen
con : WOpen
anyTy : WOpen
openTy : WOpen
closed : WOpen
openInTy : WTy
closedInTy : WTy
utup : WClosed

arg : WFun -> WTy
res : WFun -> WTy
member : WTy -> WExp -> WCo
memberOpen : WOpen → WExp → WCo
memberClosed : WClosed → WExp -> WCo
conjunct : WCo -> WCo -> WCo
eq : WExp -> WExp -> WCo
pairTy : WTy -> WTy -> WTy
pair : WExp -> WExp -> WExp
intersect : WTy -> WTy -> WTy
intersectOpen : WOpen → WOpen → WOpen
union : WTy -> WTy -> WTy
unionOpen : WOpen → WTy → WOpen
unionClosed : WClosed → WClosed → WClosed 
conToFun : WCon -> WFun
openToTy : WOpen -> WTy
closedToTy : WClosed -> WTy

data WExp where
  Tagged : WTag → WExp
  Var : Nat → WExp
  App : (f : WCon) → WTypedExp (arg $ conToFun f) → WExp
  -- TODO: Upgrade to lam-case
  -- Matchable = [a, b, f: a ~> b, x: a] 'f(x)
  -- (i.e: We have evidence that it was constructed with a Con)
  Lam : (v : Nat) → (t : WTy) → (u : WTy)
      → ({{WDict (member t $ Var v)}} → WTypedExp u) → WExp 

data WOpen where
  IsOpen : (e : WExp) → {{d : WDict $ member openInTy e}} → WOpen

unwrapOpen : WOpen -> WExp
unwrapOpen (IsOpen e) = e

data WTypedExp where
  Is : ∀ {t} → (e : WExp) → {{d : WDict $ member t e}} → WTypedExp t

unwrap : ∀ {t} -> WTypedExp t -> WExp
unwrap (Is e) = e

WCon  = WTypedExp $ openToTy con  
WFun  = WTypedExp $ openToTy fun
WCo   = WTypedExp $ openToTy co
WUTup = WTypedExp $ closedToTy utup
WAny  = WTypedExp $ openToTy anyTy
WClosed = WTypedExp $ openToTy closed

data WInst : WOpen -> WExp -> Set

data WClosedMem : WClosed -> WExp -> Set where

-- Replacing the final `WDict` with `wdict` as defined below (so carrying
-- evidence of the index being correct vs the index being inherently the
-- correct one) appears to sometimes help with pattern-matching unification
-- (so-called "green slime") errors
--
-- The consequence is that working with them becomes a bit more clunky and that
-- having the constructors be `instance`s no longer works (because they 
-- immediately match any desired `WDict` constraint). I would like to try and
-- avoid this for now...
wdict : WCo → Set
wdict c = ∀ {idx} → {idx ≡ c} → WDict idx

data WDict where
  -- Primitive
  instance DConjunct : ∀ {co1 co2} → {{WDict co1}} → {{WDict co2}} 
                     → WDict $ conjunct co1 co2
  instance DEq : ∀ {e} → WDict $ eq e e

  -- Open type instances
  -- We cannot make them `instance`s without risking overlap
  DInst : ∀ {e t} → {{i : WInst t e}} → WDict $ member (openToTy t) e
  -- Closed type membership axioms
  DClosedMem : ∀ {e t} → {{WClosedMem t e}} 
             → WDict $ member (closedToTy t) e
  
  
  -- TODO: This should really be inside `WInst`, but here prevents 
  --  non-termination error
  instance DOpenInOpen : WDict $ member openInTy $ Tagged TOpen

  -- TODO:
  -- This *should* be redundant, added to try and avoid non-termination
  -- errors

  instance DOpenSubTy : ∀ {x} → {{WDict $ member openInTy x}} 
                      → WDict $ member tyInTy x

  -- Unions/intersection rules
  instance DLhsInUnion : ∀ {l r x} → {{xInL : WDict $ member l x}} 
                       → WDict $ member (union l r) x
  instance DRhsInUnion : ∀ {l r x} → {{xInR : WDict $ member r x}}
                       → WDict $ member (union l r) x
  instance DInBothInIntersect : ∀ {l r x} → {{xInL : WDict $ member l x}}
                              → {{xInR : WDict $ member r x}}
                              → WDict $ member (intersect l r) x
  
  -- Function application
  instance DAppliedInRes : ∀ {f x} → WDict $ member (res $ conToFun f) (App f x)
  
  -- TODO: I don't think should be an axiom, but should just follow from
  -- definition of pair type!
  instance DPairInPairTy : ∀ {a b x y}
                         → {{xInA : WDict $ member a x}}
                         → {{yInB : WDict $ member b y}}
                         → WDict $ member (pairTy a b) (pair x y)

  -- TODO: Replace forall encoding with subtyping!
  -- TODO: Below all require knowledge that `Con : Ty` to typecheck
  -- instance DConsInCon : WDict $ member (IsTy con) $ Tagged TCons
  -- instance DConsedInCon : ∀ {x} → WDict $ member con 
  --                       $ App (Is $ Tagged TCons) x


  -- IClosedInOpen : WInst openTy $ Tagged TClosed
  -- ICoInOpen : WInst openTy $ Tagged TCo
  -- IFunInOpen : WInst openTy $ Tagged TFun
  -- IAnyInOpen : WInst openTy $ Tagged TAny 
  -- -- See comment by `DOpenInOpen` in `WDict`
  -- -- instance DOpenInOpen : WInst openTy $ Tagged TOpen

  -- -- Ideally not an axiom but should follow from the Con type
  -- IConSubFun : ∀ {f} → {{fInCon : WDict $ member (openToTy con) f}} 
  --                     → WInst fun f
  -- IMemberInCon : WInst con $ Tagged TMember

data WInst where
  IClosedInOpen : WInst openTy $ Tagged TClosed
  ICoInOpen : WInst openTy $ Tagged TCo
  IFunInOpen : WInst openTy $ Tagged TFun
  IAnyInOpen : WInst openTy $ Tagged TAny 
  -- See comment by `DOpenInOpen` in `WDict`
  -- instance DOpenInOpen : WInst openTy $ Tagged TOpen

  -- Ideally not an axiom but should follow from the Con type
  IConSubFun : ∀ {f} → {{fInCon : WDict $ member (openToTy con) f}} 
                      → WInst fun f
  IAllInAny : ∀ {e} → WInst anyTy e
  IMemberInCon : WInst con $ Tagged TMember
  IMemberXInCon : ∀ {x} → WInst con $ App (Is (Tagged TMember) {{ d = DInst {{i = IMemberInCon}}}}) x
  -- We (eventually) should remove this to avoid being able to unbound `Var`s
  IConsInCon : WInst con $ Tagged TCons
  IConsXInCon : ∀ {x} → WInst con $ App (Is (Tagged TCons) {{d = DInst {{i = IConsInCon}}}}) x

instance DClosedInOpen = DInst {{i = IClosedInOpen}}
instance DCoInOpen     = DInst {{i = ICoInOpen}}
instance DFunInOpen    = DInst {{i = IFunInOpen}}
instance DAnyInOpen    = DInst {{i = IAnyInOpen}}
instance DConSubFun    : ∀ {f} → {{fInCon : WDict $ member (openToTy con) f}} 
                       → WDict $ member (openToTy fun) f
DConSubFun             = DInst {{i = IConSubFun}}
instance DAllInAny     : ∀ {e} → WDict $ member (openToTy anyTy) e
DAllInAny              = DInst {{i = IAllInAny}}

instance DMemberInCon  = DInst {{i = IMemberInCon}}
instance DMemberXInCon : ∀ {x} → WDict $ member (openToTy con) 
                       $ App (Is $ Tagged TMember) x
DMemberXInCon          = DInst {{i = IMemberXInCon}}

instance DConsInCon    = DInst {{i = IConsInCon}}
instance DConsXInCon   : ∀ {x} → WDict $ member (openToTy con) 
                       $ App (Is $ Tagged TCons) x
DConsXInCon            = DInst {{i = IConsXInCon}}


memberOpen t e = member (openToTy t) e
memberClosed t e = member (closedToTy t) e

openInTy = openToTy openTy

co     = IsOpen (Tagged TCo)
fun    = IsOpen (Tagged TFun)
anyTy  = IsOpen (Tagged TAny)
openTy = IsOpen (Tagged TOpen) {{d = DOpenInOpen}}
closed = IsOpen (Tagged TClosed) 

conToFun (Is e) = Is e

-- (λ _ → openToTy ty) ∷ (λ _ → openToTy ty) ∷ []
tyMembers' : ∀ {t e} → WInst t e → List ((self : WClosed) → WTy)

tyMembers'' : ∀ {t e} → WDict (member (openToTy t) e) → List ((self : WClosed) → WTy)

-- This, arguably, could even work as a member of the `ty` type
-- This would VERY recursive (and hard to implement) though
tyMembers : WOpen → List ((self : WClosed) → WTy)
tyMembers (IsOpen _ {{d}}) = tyMembers'' d

-- a <: b = for(x: a) { a :: b }
sub : WTy → WTy → WCo

-- Inj = (f: Fun) <<= for(x: arg(f), y: arg(f)) { f(x) ~ f(y) => x ~ y }
inj : WOpen

-- Gen = (f: Fun) <<= for(g: Gen, x: arg(f) & arg(g)) { f(x) ~ g(x) => f ~ g }
gen : WOpen

-- Con = Inj & Gen
con = intersectOpen inj gen

-- WTy = WTypedExp tyInTy
data WTy where
  IsTy : (e : WExp) → {{d : WDict $ member tyInTy e}} → WTy

tyInTy = openToTy ty

openToTy (IsOpen e) = IsTy e
  -- {{d = subst (λ x → WDict $ member x e) openToTyTyIsUnion DLhsInUnion}}

ty = unionOpen openTy $ openToTy closed


closedInTy = openToTy closed


nil : WExp

promote : WExp → WClosed

-- UTup = 'Nil | [h, t] '(h :. t)
utup = unionClosed (promote nil) (consed)
  where
    consed : WClosed
    consed = todo


  -- Curried (operator) constructor application
BiApp : (f : WCon) → (x : WTypedExp $ arg $ conToFun f) 
      → {{ fxInCon : WDict $ member (openToTy con) $ App f x }}
      → (y : WTypedExp $ arg $ conToFun $ Is (App f x))
      → WExp
BiApp f x y = App (Is $ App f x) y

arg (Is (Tagged TMember)) = openToTy ty
arg (Is (App (Is (Tagged TMember)) x)) = openToTy anyTy
arg _ = todo

res (Is (App (Is (Tagged TMember)) x)) = openToTy co
res _ = todo


-- We should be able to remove these postulates after we define arg
-- (worst-case turn them into forward declarations and prove after defining it)
argMemberIsTy : openToTy ty ≡ arg (Is $ Tagged TMember)
argMemberIsTy = refl

arg2MemberXIsAny : ∀ {x} → openToTy anyTy 
                 ≡ arg (Is $ App (Is $ Tagged TMember) x)
arg2MemberXIsAny = refl

resMemberIsCo : ∀ {x} → res (Is $ App (Is $ Tagged TMember) x)
              ≡ openToTy co
resMemberIsCo = refl


typedTyToTy : WTypedExp tyInTy → WTy
typedTyToTy (Is e) = IsTy e

tyToTypedTy : WTy → WTypedExp tyInTy
tyToTypedTy (IsTy e) = Is e

-- openToTy anyTy != arg (conToFun $ Is (App (Is (Tagged TMember)) t))

-- {-# TERMINATING #-}
member t e
  = subst WTypedExp (resMemberIsCo {x = t'}) $ Is $ BiApp (Is $ Tagged TMember) t' e'
    where
      t' = subst WTypedExp argMemberIsTy $ tyToTypedTy t 
      e' = subst WTypedExp arg2MemberXIsAny $ Is e

postulate argConsIsAny : openToTy anyTy ≡ arg (Is $ Tagged TCons)

postulate arg2ConsUTup : ∀ {x} → closedToTy utup
                       ≡ arg (Is $ App (Is $ Tagged TCons) x) 

postulate resArgInUTup : ∀ {x} → res (Is $ App (Is $ Tagged TCons) x) 
                       ≡ closedToTy utup

cons : WExp -> WUTup -> WUTup
cons x y
  = subst WTypedExp resArgInUTup $ Is $ BiApp (Is $ Tagged TCons) x' y'
    where
      x' = subst WTypedExp argConsIsAny $ Is x
      y' = subst WTypedExp arg2ConsUTup y


foo : WExp → WCo
foo = member tyInTy

{-# INJECTIVE foo #-}

memberInj : ∀ {x y} → foo x ≡ foo y → x ≡ y
memberInj refl = refl

-- tyMembers'' (DInst  {{i}}) = tyMembers' i
-- tyMembers'' _ = todo