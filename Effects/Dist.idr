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

partial
handleDist : Prog (Dist :: es) a -> Prog (Observe :: Sample :: es) a
handleDist (Op op k) = case discharge op of
  _ => ?t
handleDist (Val a)   = Val a