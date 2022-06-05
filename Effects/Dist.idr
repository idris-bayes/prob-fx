module Effects.Dist

data Dist : a -> Type where
  Normal    : Double -> Double -> Dist Double
  Bernoulli : Double -> Dist Bool
  Discrete  : List Double -> Dist Int
  Uniform   : Double -> Double -> Dist Double
