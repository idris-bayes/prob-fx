module Wasabaye2.ModelIx

import Data.List.Elem
import Data.List
import Data.Maybe

||| Primitive distributions
data PrimDist : a -> Type where
  Normal    : (mu : Double) -> (std : Double) -> PrimDist Double
  Bernoulli : (p : Double) -> PrimDist Bool
  Uniform   : (min : Double) -> (max : Double) -> PrimDist Double

||| Model indexed by an environment of random variables
data ModelIx : (env : List (String, Type)) -> (x : Type) -> Type where
  Pure      : a -> ModelIx [] a
  (>>=)     : {env1, env2 : _} -> ModelIx env1 a -> (a -> ModelIx env2 b) -> ModelIx (env1 ++ env2) b
  Dist      : PrimDist a -> (y : String) -> ModelIx [(y, a)] a
-- | "If" returns a model indexed by both branches' sample spaces.
  If        : {env1, env2 : _} -> (b : Bool) -> (m1 : ModelIx env1 a) -> (m2 : ModelIx env2 a) -> ModelIx (env1 ++ env2) a

-- | "iF" returns a model indexed by one of the branches' sample space.
iF : Bool -> (ModelIx omega1 a) -> (ModelIx omega2 a) -> (b ** ModelIx (if b then omega1 else omega2) a)
iF True m1 m2  = (True ** m1)
iF False m1 m2 = (False ** m2)

normal mu std y    = Dist (Normal mu std) y
uniform min max y  = Dist (Uniform min max) y
bernoulli p y      = Dist (Bernoulli p) y

-- | Example models
-- Example 1
exampleModelIx1 : ModelIx [("x", Double)] Double
exampleModelIx1 = do
  x <- normal 0 2 "x"
  Pure x

exampleModelIx1Impl : ModelIx [("x", Double)] Double
exampleModelIx1Impl = do
  ((>>=) {env1 = [("x", Double)]}) (normal 0 2 "x")  (\x => Pure x)

-- Example 2 
exampleModelIx2 : ModelIx [("b", Bool), ("y_0", Double), ("y_1", Double)] Double
exampleModelIx2 = do
  b <- bernoulli 0.5 "b"
  y <- If b (normal 1 1 "y_0") (normal 0 1 "y_1")
  Pure y

-- Example 3
exampleModelIx3 : ModelIx [("b", Bool)] (b ** ModelIx (if b then [("y_0", Double)] else [("y_1", Double)]) Double)
exampleModelIx3 = do
  b <- bernoulli 0.5 "b"
  let m = iF b (normal 1 1 "y_0") (normal 0 1 "y_1")
  case m of (True ** m1)  => Pure (True ** m1)
            (False ** m2) => Pure (False ** m2)

||| Environment
public export
data Env : List (String, Type)  -> Type where
  ENil  : Env []
  ECons : (var : String) -> (val : Maybe a) -> Env env -> Env ((var, a) :: env)

decompEnv : {xs : _} -> Env (xs ++ ys) -> (Env xs, Env ys)
decompEnv {xs = Nil} es = (ENil, es)
decompEnv {xs = ((var, ty) :: vs)} (ECons var val envs) 
  = let (xs_rest, ys) = decompEnv {xs=vs} envs
    in  (ECons var val xs_rest, ys)

||| Evaluating a model under an environment
public export 
evalModelIx : ModelIx env a -> (Env env -> a)
evalModelIx (Pure x) ENil = x
evalModelIx ((>>=) mx k) env with (decompEnv env)
  _ | (env_xs, env_ys) = let x = evalModelIx  mx env_xs
                         in  evalModelIx (k x) env_ys
evalModelIx (If b m1 m2) env with (decompEnv env)
  _ | (env_xs, env_ys) = if b then evalModelIx m1 env_xs 
                         else evalModelIx m2 env_ys
evalModelIx (Dist (Normal mu std) var)   (ECons var val ENil) = fromMaybe (-1) val
evalModelIx (Dist (Uniform min max) var) (ECons var val ENil) = fromMaybe (-1) val
evalModelIx (Dist (Bernoulli p) var)     (ECons var val ENil) = fromMaybe True val

-- | Examples: Test evaluating a concrete ModelIx example under an environment instance.
-- Example 2
test_evalModelIx2 : Double
test_evalModelIx2 = evalModelIx exampleModelIx2 (ECons "b" (Just True) (ECons "y_0" (Just 1.0) (ECons "y_1" Nothing ENil)))

-- Example 3
test_evalModelIx3 : Double
test_evalModelIx3 = 
  let branchedModel : (b ** ModelIx (if b then [("y_0", Double)] else [("y_1", Double)]) Double) 
        = evalModelIx exampleModelIx3 (ECons "b" (Just True) ENil)
  in  case branchedModel of (True  ** m1) => evalModelIx m1 (ECons "y_0" (Just 1.0) ENil)
                            (False ** m2) => evalModelIx m2 (ECons "y_1" Nothing ENil)


namespace ProbProg
  ||| Probabilistic program 
  data ProbProg : (env : List (String, Type)) -> (x : Type) -> Type where
    Pure    : a -> ProbProg [] a
    (>>=)   : {env1, env2 : _} -> ProbProg env1 a -> (a -> ProbProg env2 b) -> ProbProg (env1 ++ env2) b
    Sample  : PrimDist a -> (y : String) -> ProbProg env a
    Observe : PrimDist a -> a -> (y : String) -> ProbProg env a
    If      : {env1, env2 : _} -> (b : Bool) -> (m1 : ProbProg env1 a) -> (m2 : ProbProg env2 a) -> ProbProg (env1 ++ env2) a

  translateModelIx : ModelIx env a -> (Env env -> ProbProg env a)
  translateModelIx (Pure x) ENil = Pure x
  translateModelIx ((>>=) mx k) env with (decompEnv env)
    _ | (env_xs, env_ys) = let px = translateModelIx mx env_xs
                               pk = \x => translateModelIx (k x) env_ys
                           in  (>>=) px pk
  translateModelIx (If b m1 m2) env with (decompEnv env)
    _ | (env_xs, env_ys) = If b (translateModelIx m1 env_xs)
                                (translateModelIx m2 env_ys)
  translateModelIx (Dist d var) (ECons var maybe_val ENil) = case maybe_val of
    Just val  => Observe d val var
    Nothing   => Sample  d var

  -- | Examples: Test translating a concrete ModelIx example to a Sample and Observe probabilistic program.
  -- Example 2
  test_translateModelIx2 : ProbProg  [("b", Bool), ("y_0", Double), ("y_1", Double)] Double
  test_translateModelIx2 = translateModelIx exampleModelIx2 (ECons "b" (Just True) (ECons "y_0" (Just 1.0) (ECons "y_1" Nothing ENil)))

  -- Example 3
  test_translateModelIx3 : ProbProg [("b", Bool)] (b ** ProbProg (if b then [("y_0", Double)] else [("y_1", Double)]) Double)
  test_translateModelIx3 = do
    let branchedModel = translateModelIx exampleModelIx3 (ECons "b" (Just True) ENil)
    branchedModel >>= (\dp => case dp of
                        (True ** m1) =>  let probProg1 : ProbProg [("y_0", Double)] Double 
                                                              = translateModelIx m1 (ECons "y_0" (Just 1.0) ENil) 
                                         in  Pure (True ** probProg1)
                        (False ** m2) => let probProg2 : ProbProg [("y_1", Double)] Double 
                                                             = translateModelIx m2 (ECons "y_1" (Just 1.0) ENil) 
                                         in  Pure (False ** probProg2))

-- ||| To think about:
-- 1. a) Test evaluating a concrete ModelIx example under an environment instance.
--    b) Test translating a concrete ModelIx example to a Sample and Observe probabilistic program.
-- 2. How to implement environments that assign traces of values to single variable names. 
--      - Is it possible to read the first value from a variable's trace, put the trace back in the environment, and read the next value from the trace the next time we encounter the variable again? 
--      - Maybe trying to use lists defeats the purpose of this research; perhaps we're translating ideas from Haskell wasabaye too hard, whereas we want to see how expressively we can capture the sample space; perhaps we can't really take advantage of dependent types in the list-approach. Assuming we stick to assigning single values to observable variables, each call to a primitive distribution should have a unique variable name. When we want to have a RV represent multiple values, we could instead provide a multivariate primitive distribution.
-- 3. If the order of values in the environment/trace is determined by the type of the model, are their corresponding variable names essentially redundant (assuming we don't take a list approach)?
-- 4. How to implement distributions that _don't_ take a variable name. Can we take advantage of Idris's variable number of arguments functionality.