module ProbFX2.ModelIx

import Data.List.Elem
import Data.List
import Data.Maybe

||| Primitive distributions
public export
data PrimDist : a -> Type where
  Normal    : (mu : Double) -> (std : Double) -> PrimDist Double
  Bernoulli : (p : Double) -> PrimDist Bool
  Uniform   : (min : Double) -> (max : Double) -> PrimDist Double

||| Model indexed by an environment of random variables
public export
data ModelIx : (env : List (String, Type)) -> (x : Type) -> Type where
  Pure      : a -> ModelIx [] a
  (>>=)     : {env1, env2 : _} -> ModelIx env1 a -> (a -> ModelIx env2 b) -> ModelIx (env1 ++ env2) b
  Dist      : PrimDist a -> (y : String) -> ModelIx [(y, a)] a
-- | "If" returns a model indexed by both branches' sample spaces.
  If        : {env1, env2 : _} -> (b : Bool) -> (m1 : ModelIx env1 a) -> (m2 : ModelIx env2 a) -> ModelIx (env1 ++ env2) a

-- | "iF" returns a model indexed by one of the branches' sample space.
public export
iF : Bool -> (ModelIx omega1 a) -> (ModelIx omega2 a) -> (b ** ModelIx (if b then omega1 else omega2) a)
iF True m1 m2  = (True ** m1)
iF False m1 m2 = (False ** m2)

public export
normal : Double -> Double -> (y : String) -> ModelIx [(y, Double)] Double
normal mu std y    = Dist (Normal mu std) y
public export
uniform : Double -> Double -> (y : String) -> ModelIx [(y, Double)] Double
uniform min max y  = Dist (Uniform min max) y
public export
bernoulli : Double -> (y : String) -> ModelIx [(y, Bool)] Bool
bernoulli p y      = Dist (Bernoulli p) y

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

namespace ProbProg
  ||| Probabilistic program 
  public export
  data ProbProg : (env : List (String, Type)) -> (x : Type) -> Type where
    Pure    : a -> ProbProg [] a
    (>>=)   : {env1, env2 : _} -> ProbProg env1 a -> (a -> ProbProg env2 b) -> ProbProg (env1 ++ env2) b
    Sample  : PrimDist a -> (y : String) -> ProbProg env a
    Observe : PrimDist a -> a -> (y : String) -> ProbProg env a
    If      : {env1, env2 : _} -> (b : Bool) -> (m1 : ProbProg env1 a) -> (m2 : ProbProg env2 a) -> ProbProg (env1 ++ env2) a
 
  public export
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
