{-# OPTIONS --no-positivity-check #-}
{-# OPTIONS --type-in-type #-}

open import Agda.Builtin.Nat
open import Function.Base
open import Data.List.Base
open import Relation.Binary.PropositionalEquality.Core
open import Data.Maybe.Base

-- Utils

postulate todo : ∀ {a : Set} → a

infer : ∀ {t : Set} → {{t}} → t
infer {{d}} = d

-- End Utils

-- Things went quite wrong the previous attempt. It appears that it is a LOT
-- easier to get Agda's typechecker to loop than Idris2 (every function I have 
-- asserted termination for via a pragma has ended up causing a compile-time
-- loop so I need to be a lot more careful with where I use helper functions)

data WCtx : Set where

data WTag : Set where
  -- TODO: Define `DepCons` and define ordinary cons in terms of it
  TCons : WTag
  TUnit : WTag
  -- TODO: Define `DepFun` and define 
  -- `Fun = (f: DepFun) <<= { depRes(f) ~ [t: Ty] const(t) }`
  -- TODO: Swap TCon for TFun and define TCon via Fun + Inj + Gen
  -- TCon : WTag
  TArg : WTag
  TRes : WTag
  TMember : WTag
  TUnion : WTag
  TConjunct : WTag
  TImplies : WTag
  TInter : WTag
  TCo : WTag
  TAny : WTag
  TFor : WTag
  TOpen : WTag
  TClosed : WTag
  TPromote : WTag
  TSuchThat : WTag
  T : Nat → WTag


data WExp : Set

-- Conceptually this should be indexed with a `WTy` but we index with a `WExp`
-- instead to avoid problematic recursion
data WTypedExp : WExp → Set
-- Conceptually this should be indexed with a `WCo` but we index with a `WExp`
-- instead to avoid problematic recursion
data WDict : WExp → Set


WCon : Set
WCo : Set
WUTup : Set
WAny : Set
WClosed : Set
WOpen : Set
WTy : Set



-- TODO: Relax to `WFun → WTy`
arg : WCon → WExp
-- Dependent functions
depRes : (f : WCon) → WTypedExp (arg f) → WExp

data WApp : Set

openTy : WOpen

-- The problem:
-- :: takes a type as it's second argument
-- Types must be proved as ∈ Ty
-- Therefore, I don't see a way around the function being mentioned inside it's
-- own type signature
-- Solution: 
-- We define ∈, which is NOT ::
-- Instead, x ∈ y = y :: Ty /\ x :: y  
_∈_ : WExp → WExp → WExp

-- data Bound : Set where
--   Named : Nat → Bound
--   Discard : Boun∈d

applyIfJust : ∀ {a b} → (a → b → b) → Maybe a → b → b
applyIfJust f (just x) = f x
applyIfJust _ nothing = id

data WTypedExp where
  -- TODO: Relax depRestriction on `t` from `Open` to `Ty`
  Is : ∀ {t} → (e : WExp) → {{d : WDict $ e ∈ t}} → WTypedExp t

data WExp where
  Tagged : WTag → WExp
  Var : Nat → WExp
  -- App (defined infix for convenience)
  _$$_ : (f : WCon) → WTypedExp (arg f) → WExp
  -- TODO: Generalise into lambda-case (i.e: formalise pattern-matching)
  Lam : (v : Maybe Nat) → (t : WExp) → {{tInOpen : WDict $ t ∈ Tagged TOpen}} 
      → applyIfJust (λ v r → {{WDict $ Var v ∈ t}} → r) v WExp
      → WExp
  -- Function types are primitive in WTy2 to solve a challenging case of 
  -- recursion (`(->)` is itself a function)
  -- Note even defining function types in terms of pi-types, which perhaps seems
  -- natural, is inconsistent
  -- The below definition of primFun will fail termination checking
  -- > primFun (Is a) (Is b) = PrimPi (Is a) (Is (Lam nothing a b))
  -- TODO: Relax to `WTy → WTy → WExp`
  PrimFun : WOpen → WOpen → WExp
  -- TODO: Relax to `(t : WTy) → WTypedExp (PrimFun t $ ty) → WExp
  -- I am *pretty* confident that although ordinary function types are a subset
  -- of pi-types, to define pi-types, we need to first have ordinary functions
  PrimPi : (t : WOpen) → WTypedExp (PrimFun t openTy) → WExp

pattern lamConst t e = Lam nothing t e
-- Unfortunately, instance arguments do not appear to be handled well/properly
-- with pattern synonyms (specifically, I find that `e` is forced to be of type
-- `WExp` instead of `{{WDict $ Var v ∈ t}} → WExp` when using the synonym)
-- pattern lamBind v t e = Lam (just v) t e

lamBind : (v : Nat) → (t : WExp) → {{tInOpen : WDict $ t ∈ Tagged TOpen}} 
           → ({{WDict $ Var v ∈ t}} → WExp) → WExp
lamBind v t e = Lam (just v) t e

-- Con = Inj & Gen
con : WExp
-- WCon = WTypedExp $ Tagged TCon
WCon = WTypedExp $ con
WCo = WTypedExp $ Tagged TCo
WAny = WTypedExp $ Tagged TAny
WClosed = WTypedExp $ Tagged TClosed
WOpen = WTypedExp $ Tagged TOpen

primApp : ∀ {a b} → {{aInOpen : WDict $ a ∈ Tagged TOpen}} 
        → (f : WTypedExp $ PrimFun (Is a) b) → WTypedExp a → WExp

-- TODO: Relax/strengthen to `WTy → WAny → WCo`

unwrap : ∀ {t} → WTypedExp t → WExp
unwrap (Is x) = x

depRes (Is (Is (Tagged TMember) $$ _)) _ = Tagged TCo
depRes (Is (Is (Tagged TConjunct) $$ _)) _ = Tagged TCo
depRes (Is (Tagged TPromote)) _ = Tagged TOpen -- TODO: Change to TClosed!
depRes _ _ = todo

-- Return type of non-dependent function
res : ∀ {e} → (f : WCon) 
    → {{depResIsConst : depRes f ≡ λ (_ : WTypedExp $ arg f) → e}} → WExp
res {e} _ = e

_∧_ : WCo → WCo → WExp

_⇒_ : WCo → WCo → WExp

_=>_ : (c : WExp) → {{cInCo : WDict $ c ∈ Tagged TCo}} 
     → ({{WDict c}} → WCo) → WExp


dictIndInCo : ∀ {c} → {{WDict c}} → WDict $ c ∈ Tagged TCo

data WDict where
  instance DConjunct : ∀ {co1 co2} → {{l : WDict co1}} → {{r : WDict co2}} 
                     → WDict
                     $ Is co1 {{d = dictIndInCo}} ∧ Is co2 {{d = dictIndInCo}}

  DImplies : ∀ {co1 co2} → {{{{WDict co1}} → WDict co2}}
           → {{co1InCo : WDict $ co1 ∈ Tagged TCo}} 
           → {{co2InCo : WDict $ co2 ∈ Tagged TCo}}
           → WDict $ Is co1 ⇒ Is co2

  instance DConjunctInCon : WDict $ Tagged TConjunct ∈ con
  instance DConjunctInCon2 : ∀ {x} → WDict $ (Is (Tagged TConjunct) $$ x) 
                           ∈ con
  
  instance DMemberInCon : WDict $ Tagged TMember ∈ con
  instance DMemberInCon2 : ∀ {x} → WDict $ (Is (Tagged TMember) $$ x)
                         ∈ con

  instance DPromoteInCon : WDict $ Tagged TPromote ∈ con

  instance DOpenInOpen : WDict $ Tagged TOpen ∈ Tagged TOpen
  instance DCoInOpen : WDict $ Tagged TCo ∈ Tagged TOpen
  
  -- TODO: Eventually remove this to enforce correct scoping
  instance DAllInAny : ∀ {x} → WDict $ x ∈ Tagged TAny

  instance DAppliedInRes : ∀ {f x} → WDict $ (f $$ x) ∈ depRes f x

  instance PrimFunInOpen : ∀ {a b} → WDict $ PrimFun a b ∈ Tagged TOpen

  instance DSuchThatInCon : WDict $ Tagged TSuchThat ∈ con
  instance DSuchThatInCon2 : ∀ {t} → WDict $ (Is (Tagged TSuchThat) $$ t) ∈ con

  -- TODO: Generalise to cover lambdas which don't discard their argument
  instance LamInPrimFun : ∀ {t b u} → {{bInU : WDict $ b ∈ u}} 
                        → {{tInOpen : WDict $ t ∈ Tagged TOpen}}
                        → {{uInOpen : WDict $ u ∈ Tagged TOpen}}
                        → WDict $ lamConst t b ∈ PrimFun (Is t) (Is u)
  -- Ugh, we seemingly have to provide the body a dictionary here to write this
  -- typing rule.
  instance lamBindInPrimFun : ∀ {v t u} {b : {{WDict $ Var v ∈ t}} → WExp} 
                            → {{bInU : WDict $ b {{todo}} ∈ u}} 
                            → {{tInOpen : WDict $ t ∈ Tagged TOpen}} 
                            → WDict $ lamBind v t b ∈ u

for : (t : WOpen) → WTypedExp (PrimFun t (Is $ Tagged TCo)) → WExp

nonDep : WCon → Set
nonDep f = depRes f ≡ λ _ → Tagged TOpen

instance promoteNonDep : nonDep $ Is $ Tagged TPromote
promoteNonDep = refl

-- TODO: Relax to (t : WTy) → WTypedExp (t → Tagged TCo) → WExp 
_<<=_ : (t : WOpen) → WTypedExp (PrimFun t (Is $ Tagged TCo)) → WExp
_~_ : WExp → WExp → WExp

arg (Is (Tagged TMember)) = Tagged TOpen
arg (Is (Is (Tagged TMember) $$ _)) = Tagged TAny
arg (Is (Tagged TConjunct)) = Tagged TCo
arg (Is (Is (Tagged TConjunct) $$ _)) = Tagged TCo
arg (Is (Tagged TImplies)) = Tagged TCo
arg (Is (Is (Tagged TImplies) $$ (Is c))) 
  = Is (Tagged TCo) <<= Is (lamConst (Tagged TCo) c)
-- TODO: Relax to Ty
arg (Is (Tagged TSuchThat)) = Tagged TOpen
-- TODO: Make SuchThat dependent (should take `c -> Tagged TCo`)
-- but of course, `->` requidepRes `<<=`...
arg (Is (Is (Tagged TSuchThat) $$ c)) = PrimFun c (Is $ Tagged TCo)
arg (Is (Tagged TPromote)) = Tagged TAny
arg _ = todo


-- Injective functions
-- We call this definition "prim" in that it is not co/contra-variant as it
-- directly uses `PrimFun`
-- Inj a b = (f: a -> b) <<= { for(x: a, y: a) { f(x) ~ f(y) => x ~ y } }
primInjArrow : WOpen → WOpen → WExp
primInjArrow a@(Is a') b 
  = Is (PrimFun a b) 
  <<= (Is $ lamBind 0 (PrimFun a b) 
  $ for a $ Is $ lamBind 1 a' $ for b $ Is $ lamBind 2 a'
  $ primApp (Is $ Var 0) (Is $ Var 1) ~ primApp (Is $ Var 0) (Is $ Var 2))



biApp : (f : WCon) → (x : WTypedExp $ arg f)
      → {{fXInCon : WDict $ (f $$ x) ∈ con}} 
      → (y : WTypedExp $ arg (Is $ f $$ x)) → WExp
biApp f x y = (Is $ f $$ x) $$ y

t <<= c = biApp (Is $ Tagged TSuchThat) t c

x ∧ y = biApp (Is $ Tagged TConjunct) x y

dictIndInCo {{DConjunct}} = infer
-- Need to match on every dict, but should be a trivial proof in every case
dictIndInCo {{_}} = todo

-- Dependent and
-- x /\= y = x /\ (x => y)
--
-- In `Ty` (so without `Co` sugar) this would look a bit like
-- (/\=) : (a : Ty) -> (b : a -> Ty) -> Ty
-- a /\= b = Pair(a, (x : a) -> b(x))
-- Knowing ∀(x: a, y: a) {x ~ y}, it is obvious which `a` to provide to the
-- `snd` element (the `fst` element).
-- In other words, we have encoded dependent pairs inside `Co` manually
-- via ordinary pairs + dependent functions
_⇑_ : (x : WExp) → {{xInCo : WDict $ x ∈ Tagged TCo}} → ({{WDict x}} → WCo) 
    → WExp
-- x ⇑ y = Is x ∧ Is (x => y)  

-- TODO: Relax to `WTy → WExp → WCo`
member : WOpen → WExp → WExp 
member t x = biApp (Is $ Tagged TMember) t (Is x)

promote : WExp → WExp
promote x = Is (Tagged TPromote) $$ Is x

x ~ y = member (Is $ promote y) x

-- TODO: Relax to `WTy → WTy → WOpen`
_-→_ : WOpen → WOpen → WExp
-- (Is x) -→ (Is y) = Tagged TCon 
--   <<= (λ f → Is $ (Is $ arg f ~ x) ∧ (Is $ res f ~ y))

-- TODO: Relax to `(t : WTy) → WTy → WExp`
-- TODO: Relax definition from `Con` constraint to `Fun`
-- _-→_ : (t : WExp) → {{tInOpen : WDict $ t ∈ Tagged TOpen}} 
--      → (WTypedExp t → WOpen) → WExp
-- x -→ y = Tagged TCon <<= λ f → (Is $ arg f ~ x) ∧ (Is $ depRes f ~)

-- I am slightly worried that the definition of this will require ∈ and we will
-- get termination errors, but let's give it a try...
memberTo∈ : ∀ {x t} → {{tInOpen : WDict $ t ∈ Tagged TOpen}} 
          → {{WDict $ member (Is t) x}} 
          → WDict $ x ∈ t

x ∈ y = yInOpen ⇑ xInY
  where
    yInOpen : WExp
    yInOpen = member (Is $ Tagged TOpen) y
    -- yInOpen = Is (Is (Tagged TMember) $$ Is (Tagged TOpen)) $$ Is y

    xInYAlt : {{WDict $ y ∈ Tagged TOpen}} → WCo
    xInYAlt = Is $ member (Is y) x
    -- xInYAlt = Is $ (Is $ Is (Tagged TMember) $$ Is y) $$ Is x

    xInY : {{WDict yInOpen}} → WCo
    xInY = xInYAlt {{memberTo∈ {x = y} {t = Tagged TOpen}}}
