{-# OPTIONS --no-positivity-check #-}

open import Agda.Builtin.Nat
open import Function.Base
open import Data.List.Base
open import Relation.Binary.PropositionalEquality.Core

postulate todo : ∀ {a : Set} → a

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
res : WCon → WExp

data WApp : Set

data WExp where
  Tagged : WTag → WExp
  Var : Nat → WExp
  App : WApp → WExp

WCon = WTypedExp $ Tagged TCon
WCo = WTypedExp $ Tagged TCo
WAny = WTypedExp $ Tagged TAny
WClosed = WTypedExp $ Tagged TClosed
WOpen = WTypedExp $ Tagged TOpen

data WApp where
  _$$_ : (f : WCon) → WTypedExp (arg f) → WApp

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

arg (Is (Tagged TMember)) = Tagged TOpen
arg (Is (Tagged TConjunct)) = Tagged TCo
arg (Is (App (Is (Tagged TConjunct) $$ _))) = Tagged TCo
arg _ = todo

data WDict where
  instance DConjunctInCon : WDict $ Tagged TConjunct ∈ Tagged TCon
  instance DConjunctInCon2 : ∀ {x} → WDict $ App (Is (Tagged TConjunct) $$ x) 
                           ∈ Tagged TCon

_∧_ : WCo → WCo → WExp
x ∧ y = App $ (Is $ App $ Is (Tagged TConjunct) $$ x) $$ y

-- Options:
-- Untyped `App`, and an interpret/reduce function that checks for type errors