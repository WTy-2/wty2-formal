module Checker.TreeIntrinsic

%default total

-- Translation of https://github.com/agda/agda/issues/6966 - it works!
-- record WTy

-- TyFwd : WTy

-- data WExp : WTy -> Type

-- record WTy where
--   constructor Is
--   inner : WExp TyFwd

-- data WExp where
--   Ty    : WExp TyFwd
--   List  : WExp TyFwd -> WExp TyFwd

-- TyFwd = Is Ty

-- foo : forall a. WExp a -> Unit
-- foo Ty       = ()
-- foo (List a) = ()

-- The full example, also works!
data VarRep = Fresh | CallByVal | CallByNeed

WTy : (0 v : VarRep) -> Type

TyFwd : forall v. WTy v

data WExp : (0 v : VarRep) -> WTy v -> Type

WTy v = WExp v TyFwd

data WExpOther : (0 v : VarRep) -> WExp v TyFwd -> Type

data WExp where
  Ty    : forall v. WExp v TyFwd
  Co    : forall v. WExp v TyFwd
  Other : forall v, t. WExpOther v t -> WExp v t

TyFwd = Ty

vrep : (v : VarRep) -> WExp v Ty -> Type
vrep Fresh      = const Nat
vrep CallByNeed = WExp CallByNeed
vrep CallByVal  = ?normalised_wexp

data WDict : (0 v : VarRep) -> WExp v Co -> Type

-- In Idris2, unlike Agda, earlier constructors are not in the scope of type
-- signatures of later constructor, so we need extra forward declarations.
FnFwd : forall v   . WExp v Ty -> WExp v Ty -> WExpOther v Ty
InFwd : forall v, a. WExp v a  -> WExp v Ty -> WExpOther v Co 
PiFwd : forall v   . (t : WExp v Ty) -> (vrep v t -> WExp v Ty) 
     -> WExpOther v Ty

data WExpOther where
  Var    : forall v, t  . vrep v t                -> WExpOther v t
  Fn     : forall v     . WExp v Ty -> WExp v Ty  -> WExpOther v Ty
  Pi     : forall v     . (t : WExp v Ty) -> (vrep v t -> WExp v Ty) 
                 -> WExpOther v Ty
  -- TODO: Define pattern-matching lambdas
  Lam    : forall v, a, b. (vrep v a -> WExp v b) 
        -> WExpOther v $ Other $ FnFwd a b
  DepLam : forall v, a, f. ((x : vrep v a) -> WExp v $ f x) 
        -> WExpOther v $ Other $ PiFwd a f
  -- Promotion to singleton type
  Pro    : forall v, a   . WExp v a               -> WExpOther v Ty
  -- Type membership constraint
  In     : forall v, a   . WExp v a -> WExp v Ty  -> WExpOther v Co 
  InElim : forall v, a, b. (x : WExp v a) 
        -> {auto _ : WDict v $ Other $ InFwd x b} -> WExpOther v b
  -- Any type
  Any    : forall v      .                           WExpOther v Ty
  
FnFwd = Fn
PiFwd = Pi
InFwd = In

data WDict where
  InIntro    : forall v, a. (x : WExp v a) -> WDict v $ Other $ In x a
  InAnyIntro : forall v, a. (x : WExp v a) -> WDict v $ Other $ In x (Other Any)
  InProIntro : forall v, a. (x : WExp v a) 
            -> WDict v $ Other $ In x (Other $ Pro x)

Eq : forall v, a, b. WExp v a -> WExp v b -> WExp v Co
Eq x y = Other $ In x (Other $ Pro y)

-- Properties of `Eq`
EqRefl : forall v, a. (x : WExp v a) -> WDict v $ Eq x x
EqRefl = InProIntro

EqSymmSimp : forall v, a. (x : WExp v a) -> (y : WExp v a) 
      -> {auto x_eq_y : WDict v $ Eq x y} -> WDict v $ Eq y x
EqSymmSimp x x { x_eq_y = InProIntro _ } = InProIntro x

EqSymm : forall v, a, b. (x : WExp v a) -> (y : WExp v b) 
      -> {auto x_eq_y : WDict v $ Eq x y} -> WDict v $ Eq y x
EqSymm x x { x_eq_y = InProIntro x } = InProIntro x
-- TODO: Is this case sound, it seems like a case of non-terminating recursion?
EqSymm x y { x_eq_y = InIntro    x } = EqSymm x y

EqTransSimp : forall v, a. (x : WExp v a) -> (y : WExp v a) -> (z : WExp v a)
           -> {auto x_eq_y : WDict v $ Eq x y} 
           -> {auto y_eq_z : WDict v $ Eq y z}
           -> WDict v $ Eq x z
EqTransSimp x x x { x_eq_y = InProIntro x } { y_eq_z = InProIntro x} 
  = InProIntro x

EqTrans : forall v, a, b, c. (x : WExp v a) -> (y : WExp v b) -> (z : WExp v c)
           -> {auto x_eq_y : WDict v $ Eq x y} 
           -> {auto y_eq_z : WDict v $ Eq y z}
           -> WDict v $ Eq x z
EqTrans x x x { x_eq_y = InProIntro x } { y_eq_z = InProIntro x} 
  = InProIntro x  
-- TODO: Are these cases sound, it seems like a case of non-terminating 
-- recursion?
EqTrans x x z { x_eq_y = InProIntro x } { y_eq_z = InIntro   x } 
  = EqTrans x x z
EqTrans x y z { x_eq_y = InIntro    x }
  = EqTrans x y z
