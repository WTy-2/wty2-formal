{-# OPTIONS --no-positivity-check #-}

-- open import Data.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

data Unit : Set where
  ● : Unit

data MyBool : Set where
  True : MyBool
  False : MyBool 
  _∨_ : MyBool → MyBool → MyBool


_∧_ : MyBool → MyBool → MyBool
{-# INJECTIVE _∧_ #-}
-- x ∧ y = x ∨ y


variable b c : MyBool

data P : MyBool → Set where
  -- base : P False
  -- baseTrue : P True
  slime : ∀ {b c} → P b → P c → P (b ∧ c)
  -- slime : ∀ {b c z} → (z ≡ b ∨ c) → {{ P b }} →  {{ P c }} → P 

-- instance slime' : ∀ {b c} → {{ P b }} → {{ P c }} → P (b ∨ c)
-- slime' {{d1}} {{d2}} = slime refl {{d1}} {{d2}}

-- f : P false → Nat
-- f base = 0
-- f (slime _) = 1


g : P (False ∧ False) → Nat
-- g base = 0
g (slime _ _) = 1

-- open import Agda.Builtin.Nat
-- open import Agda.Builtin.Equality
-- open import Function.Base

-- subst : ∀ {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
-- subst P refl px = px


-- data FooRes : Set

-- proj : FooRes → Nat

-- foo : Nat → FooRes

-- data FooRes where
--   Mk : (x : Nat) → (proj (foo x) ≡ x) → FooRes

-- proj (Mk x _) = x

-- bar : ∀ {x} → x ≡ proj (foo x)

-- {-# TERMINATING #-}
-- foo x = Mk x (subst (λ y → y ≡ x) (bar {x = x}) refl)

-- bar = refl

-- open import Data.Maybe
-- open import Agda.Builtin.Nat


-- -- mutual
-- --   data Foo : Set where
-- --     MkFoo : Nat → Maybe Bar → Foo
-- --   data Bar : Set where
-- --     MkBar : Nat → Maybe Foo → Bar

-- data FooInner : Set → Set where
--   MkFoo : ∀ {a} → Nat → Maybe a → FooInner a
-- data Bar : Set where
--   MkBar : Nat → Maybe (FooInner Bar) → Bar

-- Foo : Set
-- Foo = FooInner Bar 