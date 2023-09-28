module Checker.Utils
{-


-- MTL
{-
interface MonadReader m where
  r : Type
  ask : m r
  local : {0 a: Type} -> (r -> r) -> m a -> m a
  reader : {0 a: Type} -> (r -> a) -> m a

interface MonadWriter m where
  w : Type
  writer : {0 a: Type} -> (a, w) -> m a
  tell : w -> m ()
  listen : {0 a: Type} -> m a -> m (a, w)
  pass : {0 a: Type} -> m (a, w -> w) -> m a

interface MonadState m where
  s : Type
  get : m s
  put : s -> m ()
  state : {0 a: Type} -> (s -> (a, s)) -> m a
-}

-- We break from MTL a bit for fun
interface MonadWriter m where
  w : Type
  writer : {0 a: Type} -> (a, w) -> m a
  tell : w -> m ()
  listen : {0 a: Type} -> m a -> m (a, w)
  pass : {0 a: Type} -> m (a, w -> w) -> m a

interface MonadReader m where
  r : Type
  ask : m r
  local : {0 a: Type} -> (r -> r) -> m a -> m a
  reader : {0 a: Type} -> (r -> a) -> m a

{-
interface (MonadWriter m, MonadReader m) => MonadState (m: Type -> Type) where
  s : Type
-}

 -}

public export
data Tuple : List Type -> Type where
  (::) : forall t. (h: t) -> (r: Tuple ts) -> Tuple (t :: ts)
  Nil : Tuple []