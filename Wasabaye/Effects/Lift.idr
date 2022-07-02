module Wasabaye.Effects.Lift

import Wasabaye.Prog

-- | Lift effect for a monadic computation 
public export
data Lift : (m : Type -> Type) -> Effect where
  MkLift : m a -> Lift m a

sendWithPrf : {prf : Elem f fs} -> f t -> Prog fs t
sendWithPrf = call 

public export
liftM : (prf : Elem (Lift m) es) =>  m a -> Prog es a 
liftM ma = sendWithPrf {prf} (MkLift ma)

-- | 
public export
handleLift : Monad m => Prog [Lift m] a -> m a
handleLift (Val x)   = pure x
handleLift (Op op k) = let MkLift ma = prj1 op in ma >>= handleLift . k
