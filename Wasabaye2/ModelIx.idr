module Wasabaye2.ModelIx

||| A model indexed by an environment of random variables
data ModelIx : (env : List (String, Type)) -> (x : Type) -> Type where
  Pure      : a -> ModelIx [] a
  Bind      : ModelIx env1 a -> (a -> ModelIx env2 b) -> ModelIx (env1 ++ env2) b
  Normal    : (mu : Double) -> (std : Double) -> (y : String) -> ModelIx [(y, Double)] Double
  Uniform   : (min : Double) -> (max : Double) -> (y : String) -> ModelIx [(y, Double)] Double
  Bernoulli : (p : Double) -> (y : String) -> ModelIx [(y, Bool)] Bool
-- | "If" returns a model indexed by both branches' sample spaces.
  If        : (b : Bool) -> (m1 : ModelIx omega1 a) -> (m2 : ModelIx omega2 a) -> ModelIx (omega1 ++ omega2) a

-- | "iF" returns a model indexed by one of the branches' sample space.
iF : Bool -> (ModelIx omega1 a) -> (ModelIx omega2 a) -> (b ** ModelIx (if b then omega1 else omega2) a)
iF True m1 m2  = (True ** m1)
iF False m1 m2 = (False ** m2)

pure : a -> ModelIx [] a
pure = Pure

(>>=) : ModelIx env1 a -> (a -> ModelIx env2 b) -> ModelIx (env1 ++ env2) b
(>>=) = Bind

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
interpretModelIx (Pure x) = x
interpretModelIx (Bind x k) = let v = interpretModelIx x in interpretModelIx (k v)
interpretModelIx (Normal mu std y) = 2
interpretModelIx (Uniform min max y) = ?r_15
interpretModelIx (Bernoulli p y) = True
interpretModelIx (If b m1 m2) = ?r_17



