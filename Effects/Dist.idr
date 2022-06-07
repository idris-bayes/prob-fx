module Effects.Dist

import Data.List.NonEmpty
import Prog

data PrimDist : a -> Type where
  Normal    : Double -> Double -> PrimDist Double
  Bernoulli : Double -> PrimDist Bool
  Discrete  : List Double -> PrimDist Int
  Uniform   : Double -> Double -> PrimDist Double

record Dist (a : Type) where
  constructor MkDist
  dist : PrimDist a
  obs  : Maybe a

data Observe : a -> Type where 
  MkObserve : PrimDist a -> a -> Observe a

data Sample : a -> Type where
  MkSample  : PrimDist a -> Sample a

handleDist : {es : _} -> Prog (Dist :: es) a -> Prog (Observe :: Sample :: es) a
handleDist (Val a)   = Val a
handleDist (Op op k) with (discharge op)
  _ | Left op' = Op (weaken_op $ weaken_op op') (handleDist . k)
  _ | Right d = case d.obs of Just y  => do x <- call (MkObserve d.dist y) 
                                            (handleDist . k) x
                              Nothing => call (MkSample d.dist) >>= (handleDist . k)
