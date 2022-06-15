module Experiments.ModelIxExperiment

data ModelIx : (env : List String) -> (x : Type) -> Type where
  Pure      : a -> ModelIx [] a
  (>>=)     : ModelIx xs a -> (a -> ModelIx ys b) -> ModelIx (xs ++ ys) b  
  Bernoulli : Double -> (y : String) -> ModelIx [y] Bool
  Normal    : Double -> Double -> (y : String) -> ModelIx [y] Double

-- Perhaps this should still be the union of omega1 and omega2.
iF : (b : Bool) -> (ModelIx omega1 a) -> (ModelIx omega2 a) -> (b ** ModelIx (if b then omega1 else omega2) a)
iF True m1 m2  = (True ** m1)
iF False m1 m2 = (False ** m2)

exampleModelIx : ModelIx ["b"] (b ** ModelIx (if b then [] else ["hi"]) Double)
exampleModelIx = do
  b <- Bernoulli 0.5 "b"
  let m = iF b (Pure 6) (Normal 0 1 "hi")
  case m of (True ** m1)  => Pure (True ** m1)
            (False ** m2) => Pure (False ** m2)
  -- ?t