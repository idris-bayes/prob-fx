module Wasabaye2.ModelIx

import Data.Subset

namespace ModelIxA
  data ModelIx : (env : List (String, Type)) -> (x : Type) -> Type where
    Normal    : Double -> Double -> (y : String) -> ModelIx [(y, Double)] Double
    Uniform   : Double -> Double -> (y : String) -> ModelIx [(y, Double)] Double
    Bernoulli : Double -> (y : String) -> ModelIx [(y, Bool)] Bool
  -- "If" concatenates environments from each branch
    If        : Bool   -> ModelIx omega1 a -> ModelIx omega2 a -> ModelIx (omega1 ++ omega2) a

  pure : a -> ModelIx [] a
  (>>=) : ModelIx env1 a -> (a -> ModelIx env2 b) -> ModelIx (env1 ++ env2) b


  -- "iF" returns a model from one of the two branches.
  iF : Bool -> (ModelIx omega1 a) -> (ModelIx omega2 a) -> (b ** ModelIx (if b then omega1 else omega2) a)
  iF True m1 m2  = (True ** m1)
  iF False m1 m2 = (False ** m2)

  normal    = Normal
  uniform   = Uniform
  bernoulli = Bernoulli

  -- Example 1
  exampleModelIx : ModelIx [("x", Double)] Double
  exampleModelIx = do
    x <- normal 0 2 "x"
    pure x

  exampleModelIxImpl : ModelIx [("x", Double)] Double
  exampleModelIxImpl = do
    ((>>=) {env1 = [("x", Double)]}) (normal 0 2 "x")  (\x => pure x)

  -- Example 2 
  exampleModelIx2 : ModelIx [("p", Bool), ("y", Double)] Double
  exampleModelIx2 = do
    b <- bernoulli 0.5 "p"
    y <- If b (pure 6) (Normal 0 1 "y")
    pure y

  -- Example 3
  exampleModelIx3 : ModelIx [("b", Bool)] (b ** ModelIx (if b then [] else [("y", Double)]) Double)
  exampleModelIx3 = do
    b <- Bernoulli 0.5 "b"
    let m = iF b (pure 6) (Normal 0 1 "y")
    case m of (True ** m1)  => pure (True ** m1)
              (False ** m2) => pure (False ** m2)

  interpretModelIx : ModelIx env a -> a
  interpretModelIx m = ?r