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

data WExp₀ : Set → Set₁ where
  Ty Co : ∀ {v} → WExp₀ v
  _-→_  : ∀ {v} → WExp₀ v → WExp₀ v → WExp₀ v
  Π_-→_ : ∀ {v} → WExp₀ v → (v → WExp₀ v) → WExp₀ v
  Lam   : ∀ {v} → (v → WExp₀ v) → WExp₀ v

∀WExp₀ : Set₁
∀WExp₀ = ∀ {v : Set} → WExp₀ v

VarRep₀ : Set₁
VarRep₀ = Set

record VarRep₁ : Set₁ where
  constructor ⟨_,_,_⟩
  field
    lower : VarRep₀
    vrep  : WExp₀ lower → Set
    liftv : ∀ {t} → vrep t → lower
open VarRep₁

data WExp₁ : (v : VarRep₁) → WExp₀ (lower v) → Set₁ where
  Ty Co  : ∀ {v} → WExp₁ v Ty
  _-→_   : ∀ {v} → WExp₁ v Ty → WExp₁ v Ty → WExp₁ v Ty
  Π_-→_  : ∀ {v} → (t : WExp₀ $ lower v) → (vrep v t → WExp₁ v Ty) → WExp₁ v Ty
  Lam    : ∀ {v a b} → (vrep v a → WExp₁ v b) → WExp₁ v $ a -→ b
  DepLam : ∀ {v a f} → ((x : vrep v a) → WExp₁ v $ f $ liftv v x) 
         → WExp₁ v $ Π a -→ f

∀WExp₁ : ∀WExp₀ → Set₁
∀WExp₁ t = ∀ {v} → WExp₁ v t

lift' : ∀ {v t} → WExp₁ ⟨ v , const v , id ⟩ t → WExp₀ v
-- More understandable (but slightly less specific) type signature for `lift'`
lift : ∀ {t : ∀WExp₀} → ∀WExp₁ t → ∀WExp₀
lift e = lift' e
lift' (Ty      ) = Ty
lift' (Co      ) = Co
lift' (a -→ b  ) = lift' a -→ lift' b
lift' (Π a -→ b) = Π a -→ (λ var → lift' (b var))
lift' (Lam f   ) = Lam (λ var → lift' (f var))
lift' (DepLam f) = Lam (λ var → lift' (f var))

record VarRep₂ : Set₁ where
  constructor ⟨_,_,_⟩
  field
    lower : VarRep₁
    vrep  : WExp₁ lower Ty → Set
    liftv : ∀ {t} → vrep t → VarRep₁.vrep lower Ty
open VarRep₂

data WExp₂ : (v : VarRep₂) → WExp₁ (lower v) Ty → Set₁ where
  Ty Co  : ∀ {v} → WExp₂ v Ty
  _-→_   : ∀ {v} → WExp₂ v Ty → WExp₂ v Ty → WExp₂ v Ty
  Lam    : ∀ {v a b} → (vrep v a → WExp₂ v b) → WExp₂ v $ a -→ b
  Π_-→_  : ∀ {v} → (t : WExp₁ (lower v) Ty) → (vrep v t → WExp₂ v Ty)
         → WExp₂ v Ty
  DepLam : ∀ {v a f} → ((x : vrep (lower v) a) → WExp₂ v $ f $ x) 
         → WExp₂ v $ Π a -→ f