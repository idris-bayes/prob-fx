module Wasabaye2.ModelIx

import Data.List.Elem
import Data.List
import Wasabaye2.Env


||| A model indexed by an environment of random variables
data ModelIx : (env : List (String, Type)) -> (x : Type) -> Type where
  Pure      : a -> ModelIx [] a
  Bind      : {env1, env2 : _} -> ModelIx env1 a -> (a -> ModelIx env2 b) -> ModelIx (env1 ++ env2) b
  Normal    : (mu : Double) -> (std : Double) -> (y : String) -> ModelIx [(y, Double)] Double
  Uniform   : (min : Double) -> (max : Double) -> (y : String) -> ModelIx [(y, Double)] Double
  Bernoulli : (p : Double) -> (y : String) -> ModelIx [(y, Bool)] Bool
-- | "If" returns a model indexed by both branches' sample spaces.
  If        : (b : Bool) -> (m1 : ModelIx env1 a) -> (m2 : ModelIx env2 a) -> ModelIx (env1 ++ env2) a

-- | "iF" returns a model indexed by one of the branches' sample space.
iF : Bool -> (ModelIx omega1 a) -> (ModelIx omega2 a) -> (b ** ModelIx (if b then omega1 else omega2) a)
iF True m1 m2  = (True ** m1)
iF False m1 m2 = (False ** m2)

pure : a -> ModelIx [] a
pure = Pure

(>>=) : {env1, env2 : _} -> ModelIx env1 a -> (a -> ModelIx env2 b) -> ModelIx (env1 ++ env2) b
-- (>>=) = Bind {env1} {env2}

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


namespace SubsetEnvTest
  data Subset : {0 a: Type} -> (xs, ys : List a) -> Type where
    Nil : Subset [] ys
    (::) : {0 x: a} -> (e : Elem x ys) -> Subset xs ys -> Subset (x::xs) ys

  %hint
  subsetConcatInv1 : Subset (env1 ++ env2) env  -> Subset env1 env
  %hint
  subsetConcatInv2 : Subset (env1 ++ env2) env  -> Subset env2 env  
  %hint
  subsetToElem     : Subset fs fs' -> Elem f fs -> Elem f fs'
  
  partial
  evalModelIx : (prf : Subset env env_sup) => Env env_sup -> ModelIx env a -> a
  evalModelIx ENil (Pure x)   = x
  evalModelIx env (Bind x k) = 
    let v = evalModelIx {prf = subsetConcatInv1 prf} env x 
    in  evalModelIx {prf = subsetConcatInv2 prf} env (k v)
  evalModelIx env (Normal mu std y) = 
    case get y env {prf = subsetToElem prf Here} of (v :: vs) => v
                                                    []        => (-1)
  evalModelIx env (Uniform min max y) =
    case get y env {prf = subsetToElem prf Here} of (v :: vs) => v
                                                    []        => (-1)
  evalModelIx env (Bernoulli p y) = 
    case get y env {prf = subsetToElem prf Here} of (v :: vs) => v
                                                    []        => False
  -- evalModelIx env (If b m1 m2) = 
  --   if b then evalModelIx env m1 else evalModelIx env m2


namespace StrictEnvTest

  partial
  public export
  evalModelIx : Env env -> ModelIx env a -> a
  evalModelIx ENil (Pure x)  = x
  -- evalModelIx env (Bind x k) = 
  --   let v = evalModelIx {prf = subsetConcatInv1 prf} env x 
  --   in  evalModelIx {prf = subsetConcatInv2 prf} env (k v)
  evalModelIx (ECons (y ::= (x :: xs)) ENil) (Normal mu std y) = x
  -- evalModelIx env (Uniform min max y) = ?r_15
  -- evalModelIx env (Bernoulli p y) = True
  -- evalModelIx env (If b m1 m2) = 
  --   if b then evalModelIx env m1 else evalModelIx env m2

  -- test = evalModelIx (ECons ("x" ::= [0]) ENil) exampleModelIx