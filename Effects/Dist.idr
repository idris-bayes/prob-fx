module Effects.Dist

import Freer.Prog

data Dist : a -> Type where
  Normal    : Double -> Double -> Maybe Double -> Dist Double
  Bernoulli : Double -> Maybe Bool -> Dist Bool
  Discrete  : List Double -> Maybe Int -> Dist Int
  Uniform   : Double -> Double -> Maybe Double -> Dist Double


data Observe : a -> Type where 
  MkObserve : Dist a -> a -> Observe a

data Sample : a -> Type where
  MkSample  : Dist a -> Sample a 