module Wasabaye.Effects.Lift

import Wasabaye.Prog

public export
data Lift : (m : Type -> Type) -> Effect where
  MkLift : m a -> Lift m a

send_with_prf : {prf : Elem f fs} -> f t -> Prog fs t
send_with_prf = send 

public export
liftM : (prf : Elem (Lift m) es) =>  m a -> Prog es a 
liftM ma = send_with_prf {prf} (MkLift ma)

public export
handleLift : Monad m => Prog [Lift m] a -> m a
handleLift (Val x)   = pure x
handleLift (Op op k) = let MkLift ma = prj1 op in ma >>= handleLift . k
