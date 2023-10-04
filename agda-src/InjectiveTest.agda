open import Data.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Function.Base
-- open import Relation.Binary.PropositionalEquality.Core

postulate bar : Bool → Bool
{-# INJECTIVE bar #-}

Woah : Set
f : Woah → Set
a : Woah

postulate boolEq : Bool ≡ f a
-- boolEq = refl

subst : ∀ {A : Set1} {x y : A} (P : A → Set) → x ≡ y → P x → P y
subst P refl px = px

idSet : Set → Set
idSet x = x

foo : Bool → f a
-- {-# INJECTIVE foo #-}
foo x = subst idSet boolEq $ bar x
-- foo true = false
-- foo false = true



fooInj : ∀ {x y} → foo x ≡ foo y → x ≡ y
fooInj  refl = refl

-- Conclusion: Agda will only accept an INJECTIVE pragma if the definition is
-- undefined. This means if a function relies on pragmas which have not been
-- annotated as injective, then the function will never be considered to be
-- injective!
--
-- Remaining question: is a function that uses `subst` considered not injective?
-- Answer: Not necessarily, but ONLY if the equality actually is refl. If we
-- postulate it, that is not enough (it is not a function, so claiming that
-- equality is injective does not help)...