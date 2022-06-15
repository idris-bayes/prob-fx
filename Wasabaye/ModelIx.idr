module Wasabaye.ModelIx

data ModelIx : (omega : List (String, Type)) -> (x : Type) -> Type where
  Pure      : a -> ModelIx [] a
  (>>=)     : {omega1 : _ } -> {omega2 : _ } -> ModelIx omega1 a -> (a -> ModelIx omega2 b) -> ModelIx (omega1 ++ omega2) b
  Normal    : Double -> Double -> (y : String) -> ModelIx [(y, Double)] Double
  Uniform   : Double -> Double -> (y : String) -> ModelIx [(y, Double)] Double
  Bernoulli : Double -> (y : String) -> ModelIx [(y, Bool)] Bool

normal    = Normal
uniform   = Uniform
bernoulli = Bernoulli

exampleModelIx : ModelIx [("x", Double)] Double
exampleModelIx = do
  x <- normal 0 2 "x"
  Pure x

exampleModelIxImpl : ModelIx [("x", Double)] Double
exampleModelIxImpl = do
  ((>>=) {omega1 = [("x", Double)]}) (normal 0 2 "x")  (\x => Pure x)


