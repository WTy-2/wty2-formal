open import Function.Base using (_∘_; id; const; _$_)

module Tree-MultiLevel where

-- An intrinsically-typed representation of the WTy2 language is problematic
-- because, as WTy2 is dependently typed, this requires indexing the
-- expression datatype with itself.
--
-- We could have an untyped expression datatype, but this means all typing
-- proofs (e.g: type preservation) must be written extrinsically, which is
-- a pain.
--
-- BUT, there is nothing stopping us from creating an expression datatype
-- indexed by the untyped expressions. Or indeed another expression datatype
-- indexed by the once-indexed expressions. I'm not sure how many levels is
-- appropriate, but I think this could be a powerful way to get most of the
-- benefits of type-indexing without requiring very dependent types.
--
-- For now I will try a one-level version (indexed by untyped), which should
-- enforce correct types, but could perhaps allow incorrect kinds.

data WExpUntyped : Set → Set₁ where
  Ty Co : ∀ {v} → WExpUntyped v
  _-→_  : ∀ {v} → WExpUntyped v → WExpUntyped v → WExpUntyped v
  Π_-→_ : ∀ {v} → WExpUntyped v → (v → WExpUntyped v) → WExpUntyped v
  Lam   : ∀ {v} → (v → WExpUntyped v) → WExpUntyped v

record VarRep : Set₁ where
  constructor ⟨_,_,_⟩
  field
    uvrep : Set
    vrep  : WExpUntyped uvrep → Set
    liftv : ∀ {t} → vrep t → uvrep
open VarRep

data WExp : (v : VarRep) → WExpUntyped (uvrep v) → Set₁

PolyWExpUntyped : Set₁
PolyWExpUntyped = ∀ {v : Set} → WExpUntyped v

PolyWExp : PolyWExpUntyped → Set₁
PolyWExp t = ∀ {v} → WExp v t

lift' : ∀ {v t} → WExp ⟨ v , const v , id ⟩ t → WExpUntyped v
-- More understandable (but slightly less specific) type signature for `lift'`
lift : ∀ {t : PolyWExpUntyped} → PolyWExp t → PolyWExpUntyped
lift e = lift' e

data WExp where
  Ty Co  : ∀ {v} → WExp v Ty
  _-→_   : ∀ {v} → WExp v Ty → WExp v Ty → WExp v Ty
  Π_-→_  : ∀ {v} → (t : WExpUntyped $ uvrep v) → (vrep v t → WExp v Ty) 
         → WExp v Ty
  Lam    : ∀ {v a b} → (vrep v a → WExp v b) 
         → WExp v $ a -→ b
  DepLam : ∀ {v a f} → ((x : vrep v a) → WExp v $ f $ liftv v x) 
         → WExp v $ Π a -→ f

lift' (Ty      ) = Ty
lift' (Co      ) = Co
lift' (a -→ b  ) = lift' a -→ lift' b
lift' (Π a -→ b) = Π a -→ (λ var → lift' (b var))
lift' (Lam f   ) = Lam (λ var → lift' (f var))
lift' (DepLam f) = Lam (λ var → lift' (f var))