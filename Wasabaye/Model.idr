module Wasabaye.Model

import Data.Vect
import public Wasabaye.Env
import public Wasabaye.PrimDist
import public Wasabaye.Effects.Dist
import public Wasabaye.Effects.ObsReader
import public Wasabaye.Prog

||| Model as a type-level function, specifying a program with two proofs of membership
public export
Model : (env : List (String, Type)) -> (es : List (Type -> Type)) -> (ret : Type) -> Type 
Model env es a = (Elem Dist es, Elem (ObsReader env) es) => Prog es a 

public export
runModel : (Elem Dist es, Elem (ObsReader env) es) => Model env es a -> Prog es a
runModel m = m

public export
handleCore : Env env -> Model env (Dist :: ObsReader env :: es) a -> Prog (Observe :: Sample :: es) a
handleCore env' = handleDist . handleObsRead env' . runModel

exampleModel : Model env es Int
exampleModel = pure 5

exampleHdlModel : Prog (Observe :: Sample :: []) Int
exampleHdlModel = handleCore ENil (exampleModel {env = []})

||| Distribution smart constructors
export 
uniform : Double -> Double -> (x : String) -> {auto 0 env : _} -> (prf : Observable env x Double) => Model env es Double
uniform min max x = do
  maybe_v <- call (Ask {prf} x)
  call (MkDist (Uniform min max) maybe_v (Just x))

export
uniform' : Double -> Double -> {auto 0 env : _} -> Model env es Double
uniform' min max = do
  call (MkDist (Uniform min max) Nothing Nothing)

export 
bernoulli : Double -> (x : String) -> {auto 0 env : _} -> (prf : Observable env x Bool) => Model env es Bool
bernoulli p x = do
  maybe_v <- call (Ask {prf} x)
  call (MkDist (Bernoulli p) maybe_v (Just x))

export
bernoulli' : Double -> {auto 0 env : _} -> Model env es Bool
bernoulli' p = do
  call (MkDist (Bernoulli p) Nothing Nothing)

export 
binomial : Nat -> Double -> (x : String) -> {auto 0 env : _} -> (prf : Observable env x Nat) => Model env es Nat
binomial n p x = do
  maybe_v <- call (Ask {prf} x)
  call (MkDist (Binomial n p) maybe_v (Just x))

export
binomial' : Nat -> Double -> {auto 0 env : _} -> Model env es Nat
binomial' n p = do
  call (MkDist (Binomial n p) Nothing Nothing)

export
normal : Double -> Double -> (x : String) -> {auto 0 env : _} -> (prf : Observable env x Double) => Model env es Double
normal mu sigma x = do
  maybe_v <- call (Ask {prf} x)
  call (MkDist (Normal mu sigma) maybe_v (Just x))

export
normal' : Double -> Double -> Model env es Double
normal' mu sigma = do
  call (MkDist (Normal mu sigma) Nothing Nothing)

export
beta : Double -> Double -> (x : String) -> {auto 0 env : _} -> (prf : Observable env x Double) => Model env es Double
beta a b x = do
  maybe_v <- call (Ask {prf} x)
  call (MkDist (Beta a b) maybe_v (Just x))

export
beta' : Double -> Double -> Model env es Double
beta' a b = do
  call (MkDist (Beta a b) Nothing Nothing)

export
gamma : Double -> Double -> (x : String) -> {auto 0 env : _} -> (prf : Observable env x Double) => Model env es Double
gamma a b x = do
  maybe_v <- call (Ask {prf} x)
  call (MkDist (Gamma a b) maybe_v (Just x))

export
gamma' : Double -> Double -> Model env es Double
gamma' a b = do
  call (MkDist (Gamma a b) Nothing Nothing)

export
poisson : Double -> (x : String) -> {auto 0 env : _} -> (prf : Observable env x Nat) => Model env es Nat
poisson p x = do
  maybe_v <- call (Ask {prf} x)
  call (MkDist (Poisson p) maybe_v (Just x))

export
poisson' : Double -> {auto 0 env : _} -> Model env es Nat
poisson' p = do
  call (MkDist (Poisson p) Nothing Nothing)

export
categorical : {n : Nat} -> Vect n Double -> (x : String) -> {auto 0 env : _} -> (prf : Observable env x (Fin n)) => Model env es (Fin n)
categorical ps x = do
  maybe_v <- call (Ask {prf} x)
  call (MkDist (Categorical ps) maybe_v (Just x))
  
export
categorical' : {n : Nat} -> Vect n Double -> {auto 0 env : _} -> Model env es (Fin n)
categorical' ps = do
  call (MkDist (Categorical ps) Nothing Nothing)

export
discrete : {n : Nat} -> Vect n (Double, a) -> (x : String) -> {auto 0 env : _} -> (prf : Observable env x a) => Eq a => Model env es a
discrete yps x = do
  maybe_v <- call (Ask {prf} x)
  call (MkDist (Discrete yps) maybe_v (Just x))
  
export
discrete' : {n : Nat} -> Vect n (Double, a) -> {auto 0 env : _} -> Eq a => Model env es a
discrete' yps = do
  call (MkDist (Discrete yps) Nothing Nothing)