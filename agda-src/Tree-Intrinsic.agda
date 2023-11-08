{-# OPTIONS --no-positivity-check #-}
{-# OPTIONS --erasure #-}


open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst)
open import Function.Base using (_$_; id; _∘_; const)
open import Data.Nat.Base using (ℕ)

-- Yet another formalisation attempt. On one hand I really should just commit to
-- one approach and focus on getting it working, on the other, picking the right
-- starting point could have a huge impact on how challenging this project is,
-- so I think time spent exploring other options is not entirely wasted.
--
-- This time, I want to try a more traditional intrinsically-typed approach,
-- where the expression datatype is directly indexed by possible types you could
-- give them. I am also using a variation on PHOAS for representing binding
-- constructs (true PHOAS seems not-applicable because types themselves must
-- dependent on the variable representation `v : WTy v → Set`)
module Tree-Intrinsic where

postulate todo : ∀ {𝓁} {t : Set 𝓁} → t

data @0 VarRep : Set where
  Fresh CallByVal CallByNeed : VarRep

WTy : (@0 v : VarRep) → Set

TyFwd : ∀ {@0 v} → WTy v

data WExp : (@0 v : VarRep) → WTy v → Set

WTy v = WExp v TyFwd

data WExp₁ : (@0 v : VarRep) → WExp v TyFwd → Set

data WExp where
  Ty : ∀ {@0 v}            → WExp v TyFwd
  Co : ∀ {v}               → WExp v Ty
  _₁ : ∀ {v t} → WExp₁ v t → WExp v t

TyFwd = Ty

vrep : (v : VarRep) → WExp v Ty → Set
vrep Fresh      = const ℕ
vrep CallByNeed = WExp CallByNeed
vrep CallByVal  = todo -- Normalised `WExp`

infix 0 _₁
infixr 1 _-→_
infixr 1 Π_-→_
infix 2 _∷_
infix 3 ′_

data WDict : (@0 v : VarRep) → WExp v Co → Set

data WExp₁ where
  Var     : ∀ {v t}   → vrep v t → WExp₁ v t
  _-→_    : ∀ {v}     → WExp v Ty → WExp v Ty → WExp₁ v Ty
  Π_-→_   : ∀ {v}     → (t : WExp v Ty) → (vrep v t → WExp v Ty) → WExp₁ v Ty
  -- TODO: Define pattern-matching lambdas
  Lam     : ∀ {v a b} → (vrep v a → WExp v b) → WExp₁ v $ a -→ b ₁
  DepLam  : ∀ {v a f} → ((x : vrep v a) → WExp v $ f x) → WExp₁ v $ Π a -→ f ₁
  -- Promotion to singleton type
  ′_      : ∀ {v a}   → WExp v a → WExp₁ v Ty
  -- Type membership constraint
  _∷_     : ∀ {v a}   → WExp v a → WExp v Ty → WExp₁ v Co
  ∷-elim  : ∀ {v a b} → (x : WExp v a) → ⦃ WDict v $ x ∷ b ₁ ⦄ → WExp₁ v b
  -- Any type
  Any     : ∀ {v}     → WExp₁ v Ty

data WDict where
  ∷-intro    : ∀ {v a} → (x : WExp v a) → WDict v $ x ∷ a ₁
  ∷′-intro   : ∀ {v a} → (x : WExp v a) → WDict v $ x ∷ (′ x ₁) ₁
  ∷Any-intro : ∀ {v a} → (x : WExp v a) → WDict v $ x ∷ (Any ₁) ₁

_~_ : ∀ {v a} → WExp v a → WExp v a → WExp v Co
x ~ y = x ∷ (′ y ₁) ₁

~refl : ∀ {v a} → (x : WExp v a) → WDict v $ x ~ x
~refl = ∷′-intro

-- BAD! Matching on `∷′-intro _` causes a typechecker loop. I need to try and
-- understand why...
~symm : ∀ {v a} → (x y : WExp v a)  → ⦃ WDict v $ x ~ y ⦄ → WDict v $ y ~ x
-- ~symm x x ⦃ ∷′-intro _ ⦄ = todo 

PolyWExp : (∀ {@0 v} → WExp v Ty) → Set
PolyWExp t = ∀ {@0 v} → WExp v t