module ProbFX.Model

import Data.Vect
import public ProbFX.Env
import public ProbFX.PrimDist
import public ProbFX.Effects.Dist
import public ProbFX.Effects.ObsRW
import public ProbFX.Prog

||| Model as a type-level function, specifying a program with two proofs of membership
public export
Model : (env : List (String, Type)) -> (es : List (Type -> Type)) -> (a : Type) -> Type
Model env es a = Prog (ObsRW env :: Dist :: es) a

public export
runModel : Model env es a -> Prog (ObsRW env :: Dist :: es) a
runModel m = m

||| Interpret the two effects `Dist` and `ObsRW` of a model under an input model environment,
||| yielding a probabilistic program of Observe and Sample operations that also produces an output environment
public export
handleCore : (env_in : Env env) -> (model : Model env es a) -> Prog (Observe :: Sample :: es) (a, Env env)
handleCore env_in = handleDist . handleObsRW env_in . runModel

exampleModel : Model env es Int
exampleModel = pure 5

exampleHdlModel : Prog (Observe :: Sample :: []) (Int, Env [])
exampleHdlModel = handleCore ENil (exampleModel {env = []})

||| Call a primitive distribution with an observable variable name
export
callWithObs : PrimDist a -> (x : String)
  -> {auto 0 env : _} -> (prf : Observable env x a) => Model env es a
callWithObs d x = do
  -- | Attempt to read an observation from an input model environment
  maybe_v <- call (Read {prf} x)
  -- | Invoke the operation for the primitive distribution
  v       <- call (MkDist d maybe_v x)
  -- | Write the future value to an output model environment
  call (Write {prf} x v)
  pure v

||| Call a primitive distribution with no observable variable name
export
callWithoutObs : PrimDist a -> String
  -> {auto 0 env : _} -> Model env es a
callWithoutObs d x = call (MkDist d Nothing x)

||| Smart constructors for calling primitive distributions
export
uniform :  Double -> Double -> (x : String)
  -> {auto 0 env : _} -> (prf : Observable env x Double) => Model env es Double
uniform min max  = callWithObs (Uniform min max)

export
uniform' : Double -> Double -> String -> Model env es Double
uniform' min max x = callWithoutObs (Uniform min max) x

export
bernoulli : Double -> (x : String)
  -> {auto 0 env : _} -> (prf : Observable env x Bool) => Model env es Bool
bernoulli p = callWithObs (Bernoulli p)

export
bernoulli' : Double -> String -> Model env es Bool
bernoulli' p x = callWithoutObs (Bernoulli p) x

export
binomial : Nat -> Double -> (x : String)
  -> {auto 0 env : _} -> (prf : Observable env x Nat) => Model env es Nat
binomial n p = callWithObs (Binomial n p)

export
binomial' : {auto 0 env : _} -> Nat -> Double -> String -> Model env es Nat
binomial' n p x = callWithoutObs (Binomial n p) x

export
normal : Double -> Double -> (x : String)
  -> {auto 0 env : _} -> (prf : Observable env x Double) => Model env es Double
normal mu sigma = callWithObs (Normal mu sigma)

export
normal' : Double -> Double -> String -> Model env es Double
normal' mu sigma x = callWithoutObs (Normal mu sigma) x

export
beta : Double -> Double -> (x : String)
  -> {auto 0 env : _} -> (prf : Observable env x Double) => Model env es Double
beta a b = callWithObs (Beta a b)

export
beta' : Double -> Double -> String -> Model env es Double
beta' a b x = callWithoutObs (Beta a b) x

export
gamma : Double -> Double -> (x : String)
  -> {auto 0 env : _} -> (prf : Observable env x Double) => Model env es Double
gamma a b = callWithObs (Gamma a b)

export
gamma' : Double -> Double -> String -> Model env es Double
gamma' a b x = callWithoutObs (Gamma a b) x

export
poisson : Double -> (x : String)
  -> {auto 0 env : _} -> (prf : Observable env x Nat) => Model env es Nat
poisson p = callWithObs (Poisson p)

export
poisson' : Double -> String -> Model env es Nat
poisson' p x = callWithoutObs (Poisson p) x

export
categorical : {n : Nat} -> Vect (S n) Double -> (x : String)
  -> {auto 0 env : _} -> (prf : Observable env x (Fin (S n))) => Model env es (Fin (S n))
categorical ps = callWithObs (Categorical ps)

export
categorical' : {n : Nat} -> Vect (S n) Double -> String -> Model env es (Fin (S n))
categorical' ps x = callWithoutObs (Categorical ps) x

export
discrete : {n : Nat} -> Vect (S n) (a, Double) -> (x : String)
  -> {auto 0 env : _} -> (prf : Observable env x a) => Eq a => Model env es a
discrete yps x = callWithObs (Discrete yps) x

export
discrete' : {n : Nat} -> Vect (S n) (a, Double) -> String -> Eq a => Model env es a
discrete' yps x = callWithoutObs (Discrete yps) x

export
dirichlet : {n : Nat} -> Vect (S n) Double -> (x : String)
  -> {auto 0 env : _} -> (prf : Observable env x (Vect (S n) Double)) => Model env es (Vect (S n) Double)
dirichlet ps x = callWithObs (Dirichlet ps) x

export
dirichlet' : {n : Nat} -> Vect (S n) Double -> String -> Model env es (Vect (S n) Double)
dirichlet' ps x = callWithoutObs (Dirichlet ps) x