module Wasabaye.Effects.Lift

import Control.Eff
import Control.Monad.Free

public export
data Lift : (m : Type -> Type) -> Type -> Type where
  MkLift : m a -> Lift m a

send_explicit : {prf : Has f fs} -> f t -> Eff fs t
send_explicit = lift . inj

public export
liftM : (prf : Has (Lift m) es) =>  m a -> Eff es a 
liftM ma = send_explicit {prf} (MkLift ma)

public export
handleLift : Monad m => Eff [Lift m] a -> m a
handleLift prog = case toView prog of
  Pure x   => pure x
  Bind op k => let MkLift ma = prj1 op in ma >>= handleLift . k
