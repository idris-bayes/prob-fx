||| For lifting arbitrary monadic computations into an algebraic effect setting
module ProbFX.Effects.Lift

import ProbFX.Prog

||| Lift a monadic computation `m a` into the effect `Lift m`
public export
data Lift : (m : Type -> Type) -> Effect where
  MkLift : m a -> Lift m a

||| Wrapper function for calling Lift
public export
liftM : (prf : Elem (Lift m) es) =>  m a -> Prog es a
liftM ma = call {prf} (MkLift ma)

||| Handle `Lift m`
public export
handleLift : Monad m => Prog [Lift m] a -> m a
handleLift (Val x)   = pure x
handleLift (Op op k) = let MkLift ma = prj1 op in ma >>= handleLift . k
