module Wasabaye2.ModelIx

import Data.List.Elem
import Data.List
import Wasabaye2.Env

-- data Append : 

||| A model indexed by an environment of random variables
data ModelIx : (env : List (String, Type)) -> (x : Type) -> Type where
  Pure      : a -> ModelIx [] a
  (>>=)     : {env1, env2 : _} -> ModelIx env1 a -> (a -> ModelIx env2 b) -> ModelIx (env1 ++ env2) b
  Normal    : (mu : Double) -> (std : Double) -> (y : String) -> ModelIx [(y, Double)] Double
  Uniform   : (min : Double) -> (max : Double) -> (y : String) -> ModelIx [(y, Double)] Double
  Bernoulli : (p : Double) -> (y : String) -> ModelIx [(y, Bool)] Bool
-- | "If" returns a model indexed by both branches' sample spaces.
  If        : (b : Bool) -> (m1 : ModelIx env1 a) -> (m2 : ModelIx env2 a) -> ModelIx (env1 ++ env2) a

-- | "iF" returns a model indexed by one of the branches' sample space.
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
  Pure x

exampleModelIxImpl : ModelIx [("x", Double)] Double
exampleModelIxImpl = do
  ((>>=) {env1 = [("x", Double)]}) (normal 0 2 "x")  (\x => Pure x)

-- Example 2 
exampleModelIx2 : ModelIx [("p", Bool), ("y", Double)] Double
exampleModelIx2 = do
  b <- bernoulli 0.5 "p"
  y <- If b (Pure 6) (Normal 0 1 "y")
  Pure y

-- Example 3
exampleModelIx3 : ModelIx [("b", Bool)] (b ** ModelIx (if b then [] else [("y", Double)]) Double)
exampleModelIx3 = do
  b <- Bernoulli 0.5 "b"
  let m = iF b (Pure 6) (Normal 0 1 "y")
  case m of (True ** m1)  => Pure (True ** m1)
            (False ** m2) => Pure (False ** m2)

namespace NoEnvTest
  partial 
  evalModelIx : ModelIx env a -> a                  -- | Although this is well-typed, I'm not really sure what we can do with it.
  evalModelIx (Pure x)  = x
  evalModelIx ((>>=) mx k) =
    let x = evalModelIx mx 
    in  evalModelIx (k x)
  evalModelIx (If b m1 m2) = 
    if b then evalModelIx m1 else evalModelIx m2

namespace ReaderEnvTest
  partial 
  evalModelIx : ModelIx env a -> (Env env -> a)                  -- | Although this is well-typed, I'm not really sure what we can do with it.
  evalModelIx (Pure x)  = \_ => x
  -- evalModelIx ((>>=)  mx k) =
  --   let x = evalModelIx mx 
  --   in  evalModelIx (k x)
  -- evalModelIx (If b m1 m2) = 
  --   if b then evalModelIx m1 else evalModelIx m2

  
namespace StrictEnvTestDecompVal  -- | Where "env" is literally a value of type List (String, Type)
  partial
  public export 
  evalModelIx : (env : _) ->  ModelIx env a -> a
  evalModelIx Nil (Pure x)  = x
  evalModelIx (env1 ++ env2) ((>>=) mx k) =                         -- | Evaluation of Bind is tricky
    let v = evalModelIx env1 mx 
    in  evalModelIx env2 (k v)
  evalModelIx ((y, Double) :: Nil) (Normal mu std y) = 5

namespace StrictEnvTestDecompTy  -- | Proving 

  decompEnv : {xs : _} -> Env (xs ++ ys) -> (Env xs, Env ys)
  decompEnv {xs = Nil} es = (ENil, es)
  decompEnv {xs = ((str, ty) :: vs)} (ECons (str ::= val) envs) 
    = let (xs_rest, ys) = decompEnv {xs=vs} envs
      in  (ECons (str ::= val) xs_rest, ys)

  partial
  public export 
  evalModelIx : (Env env) ->  ModelIx env a -> a
  evalModelIx ENil (Pure x)  = x
  evalModelIx env ((>>=) mx k) with (decompEnv env)
    _ | (env_xs, env_ys) = let x = evalModelIx env_xs mx 
                           in  evalModelIx env_ys (k x)

namespace SubsetEnvTest
  public export
  data Subset : {0 a: Type} -> (xs, ys : List a) -> Type where
    Nil : Subset [] ys
    (::) : {0 x: a} -> (e : Elem x ys) -> Subset xs ys -> Subset (x::xs) ys

  -- | These proofs are noisy, and i'm not sure it is possible to prove them
  %hint
  subsetId : Subset env env
  %hint
  subsetConcatInv1 : Subset (env1 ++ env2) env  -> Subset env1 env
  %hint
  subsetConcatInv2 : Subset (env1 ++ env2) env  -> Subset env2 env  
  %hint
  subsetToElem     : Subset fs fs' -> Elem f fs -> Elem f fs'
  
  -- | Need to return environment as well for it to be updated.
  partial
  public export
  ss_evalModelIx : (prf : Subset env env_sup) => Env env_sup -> ModelIx env a -> a
  ss_evalModelIx ENil (Pure x)   = x
  ss_evalModelIx env ((>>=) mx k) = 
    let x = ss_evalModelIx {prf = subsetConcatInv1 prf} env mx  
    in  ss_evalModelIx {prf = subsetConcatInv2 prf} env (k x)
  ss_evalModelIx env (Normal mu std y) = 
    case get y env {prf = subsetToElem prf Here} of (v :: vs) => v
                                                    []        => (-1)
  ss_evalModelIx env (Uniform min max y) =
    case get y env {prf = subsetToElem prf Here} of (v :: vs) => v
                                                    []        => (-1)
  ss_evalModelIx env (Bernoulli p y) = 
    case get y env {prf = subsetToElem prf Here} of (v :: vs) => v
                                                    []        => False
  ss_evalModelIx env (If b m1 m2) = 
    if b 
    then ss_evalModelIx {prf = subsetConcatInv1 prf} env m1 
    else ss_evalModelIx {prf = subsetConcatInv2 prf} env m2
