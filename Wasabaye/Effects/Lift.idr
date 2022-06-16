module Wasabaye.Effects.Lift

import Control.Eff
import Control.Monad.Free

data Lift : (m : Type -> Type) -> Type -> Type where
  MkLift : m a -> Lift m a

send_explicit : {prf : Has f fs} -> f t -> Eff fs t
send_explicit = lift . inj

liftM : (prf : Has (Lift m) es) =>  m a -> Eff es a 
liftM ma = send_explicit {prf} (MkLift ma)
