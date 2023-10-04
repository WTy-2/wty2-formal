{-# OPTIONS --no-positivity-check #-}

open import Agda.Builtin.Nat
open import Function.Base
open import Data.List.Base
open import Relation.Binary.PropositionalEquality.Core

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
  -- `Fun = (f: DepFun) <<= { res(f) ~ [t: Ty] const(t) }`
  -- TODO: Swap TCon for TFun and define TCon via Fun + Inj + Gen
  TCon : WTag
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
res : (f : WCon) → WTypedExp (arg f) → WExp

data WApp : Set

data WExp where
  Tagged : WTag → WExp
  Var : Nat → WExp
  -- App (defined infix for convenience)
  _$$_ : (f : WCon) → WTypedExp (arg f) → WExp

WCon = WTypedExp $ Tagged TCon
WCo = WTypedExp $ Tagged TCo
WAny = WTypedExp $ Tagged TAny
WClosed = WTypedExp $ Tagged TClosed
WOpen = WTypedExp $ Tagged TOpen

-- TODO: Relax/strengthen to `WTy → WAny → WCo`

-- The problem:
-- :: takes a type as it's second argument
-- Types must be proved as ∈ Ty
-- Therefore, I don't see a way around the function being mentioned inside it's
-- own type signature
-- Solution: 
-- We define ∈, which is NOT ::
-- Instead, x ∈ y = y :: Ty /\ x :: y  
_∈_ : WExp → WExp → WExp

data WTypedExp where
  -- TODO: Relax restriction on `t` from `Open` to `Ty`
  Is : ∀ {t} → (e : WExp) → {{d : WDict $ e ∈ t}} → WTypedExp t

unwrap : ∀ {t} → WTypedExp t → WExp
unwrap (Is x) = x

-- TODO: Relax to `(t : WTy) → (t → WCo) → WExp
_<<=_ : (t : WExp) → {{tInOpen : WDict $ t ∈ Tagged TOpen}} 
      → (WTypedExp t → WCo) → WExp

res (Is (Is (Tagged TMember) $$ _)) _ = Tagged TCo
res (Is (Is (Tagged TConjunct) $$ _)) _ = Tagged TCo
res _ _ = todo

_∧_ : WCo → WCo → WExp

_⇒_ : WCo → WCo → WExp

_=>_ : (c : WExp) → {{cInCo : WDict $ c ∈ Tagged TCo}} 
     → ({{WDict c}} → WCo) → WExp


dictIndIsCo : ∀ {c} → {{WDict c}} → WDict $ c ∈ Tagged TCo

data WDict where
  instance DConjunct : ∀ {co1 co2} → {{l : WDict co1}} → {{r : WDict co2}} 
                     → WDict
                     $ Is co1 {{d = dictIndIsCo}} ∧ Is co2 {{d = dictIndIsCo}}

  DImplies : ∀ {co1 co2} → {{{{WDict co1}} → WDict co2}}
           → {{co1InCo : WDict $ co1 ∈ Tagged TCo}} 
           → {{co2InCo : WDict $ co2 ∈ Tagged TCo}}
           → WDict $ Is co1 ⇒ Is co2

  instance DConjunctInCon : WDict $ Tagged TConjunct ∈ Tagged TCon
  instance DConjunctInCon2 : ∀ {x} → WDict $ (Is (Tagged TConjunct) $$ x) 
                           ∈ Tagged TCon
  
  instance DMemberInCon : WDict $ Tagged TMember ∈ Tagged TCon
  instance DMemberInCon2 : ∀ {x} → WDict $ (Is (Tagged TMember) $$ x)
                         ∈ Tagged TCon

  instance DOpenInOpen : WDict $ Tagged TOpen ∈ Tagged TOpen
  instance DCoInOpen : WDict $ Tagged TCo ∈ Tagged TOpen
  
  -- TODO: Eventually remove this to avoid scoping errors
  instance DAllInAny : ∀ {x} → WDict $ x ∈ Tagged TAny

  instance DAppliedInRes : ∀ {f x} → WDict $ (f $$ x) ∈ res f x

arg (Is (Tagged TMember)) = Tagged TOpen
arg (Is (Is (Tagged TMember) $$ _)) = Tagged TAny
arg (Is (Tagged TConjunct)) = Tagged TCo
arg (Is (Is (Tagged TConjunct) $$ _)) = Tagged TCo
arg (Is (Tagged TImplies)) = Tagged TCo
arg (Is (Is (Tagged TImplies) $$ c)) = Tagged TCo <<= (λ _ → c)
-- TODO: Relax to Ty
arg (Is (Tagged TSuchThat)) = Tagged TOpen
-- TODO: Make SuchThat dependent (should take `c -> Tagged TCo`)
-- but of course, `->` requires `<<=`...
arg (Is (Is (Tagged TSuchThat) $$ c)) = Tagged TCo
arg _ = todo



biApp : (f : WCon) → (x : WTypedExp $ arg f)
      → {{fXInCon : WDict $ (f $$ x) ∈ Tagged TCon}} 
      → (y : WTypedExp $ arg (Is $ f $$ x)) → WExp
biApp f x y = (Is $ f $$ x) $$ y

x ∧ y = biApp (Is $ Tagged TConjunct) x y

dictIndIsCo {{DConjunct}} = infer
dictIndIsCo {{_}} = todo -- Need to match on every dict

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


-- I am slightly worried that the definition of this will require ∈ and we will
-- get termination errors, but let's give it a try...
memberTo∈ : ∀ {x t} → {{tInOpen : WDict $ t ∈ Tagged TOpen}} 
          → {{WDict $ member (Is t) x}} 
          → WDict $ x ∈ t

x ∈ y = yInOpen ⇑ xInY
  where
    yInOpen : WExp
    yInOpen = Is (Is (Tagged TMember) $$ Is (Tagged TOpen)) $$ Is y

    xInYAlt : {{WDict $ y ∈ Tagged TOpen}} → WCo
    xInYAlt = Is $ (Is $ Is (Tagged TMember) $$ Is y) $$ Is x

    xInY : {{WDict yInOpen}} → WCo
    xInY = xInYAlt {{memberTo∈ {x = y} {t = Tagged TOpen}}}



-- Options:
-- Untyped `App`, and an interpret/reduce function that checks for type errors 