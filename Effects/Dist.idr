module Effects.Dist

import Freer.Prog

data PrimDist : a -> Type where
  Normal    : Double -> Double -> PrimDist Double
  Bernoulli : Double -> PrimDist Bool
  Discrete  : List Double -> PrimDist Int
  Uniform   : Double -> Double -> PrimDist Double

record Dist (a : Type) where
  constructor MkDist
  d : PrimDist a
  y : Maybe a

data Observe : a -> Type where 
  MkObserve : PrimDist a -> a -> Observe a

data Sample : a -> Type where
  MkSample  : PrimDist a -> Sample a

partial
handleDist : Prog (Dist :: es) a -> Prog (Observe :: Sample :: es) a
handleDist (Op ?s k) = ?_ 
handleDist (Val a) = Val a