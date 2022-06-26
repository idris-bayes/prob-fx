module Wasabaye.Effects.Dist

import Data.List
import Statistics.Distribution.Binomial 
import Statistics.Distribution.Normal 
import Statistics.Distribution.Uniform 
import Wasabaye.Prog
import Wasabaye.PrimDist
import System.Random

public export
record Dist (a : Type) where
  constructor MkDist
  dist : PrimDist a
  obs  : Maybe a
  tag  : Maybe String

public export
data Observe : Effect where 
  MkObserve : PrimDist a -> a -> Observe a

public export
data Sample : Effect where
  MkSample  : PrimDist a -> Sample a

public export
partial
handleDist : (prf : Elem Dist es) => Prog es a -> Prog (Observe :: Sample :: es - Dist) a
handleDist (Val x) = pure x 
handleDist (Op op k) = case discharge op {prf} of
  Right d => case d.obs of Just y  => do x <- send (MkObserve d.dist y) 
                                         (handleDist . k) x
                           Nothing => send (MkSample d.dist) >>= (handleDist . k)
  Left op' => Op (weaken1 $ weaken1 op') (handleDist . k)
