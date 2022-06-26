module Wasabaye.Model

import public Wasabaye.Env
import public Wasabaye.PrimDist
import public Wasabaye.Effects.Dist
import public Wasabaye.Effects.ObsReader
import public Wasabaye.Prog

-- | Model as a type-level function, specifying a program with two proofs of membership
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

-- | Distribution smart constructors
public export
normal : {auto 0 env : _} -> Double -> Double -> (x : String) -> (prf : Observable env x Double) => Model env es Double
normal mu sigma x = do
  maybe_v <- send (Ask {prf} x)
  send (MkDist (Normal mu sigma) maybe_v (Just x))

public export
normal' : Double -> Double -> Model env es Double
normal' mu sigma = do
  send (MkDist (Normal mu sigma) Nothing Nothing)

public export
uniform : {auto 0 env : _} -> Double -> Double -> (x : String) -> (prf : Observable env x Double) => Model env es Double
uniform min max x = do
  maybe_v <- send (Ask {prf} x)
  send (MkDist (Uniform min max) maybe_v (Just x))

public export
uniform' : Double -> Double -> Model env es Double
uniform' min max = do
  send (MkDist (Uniform min max) Nothing Nothing)
