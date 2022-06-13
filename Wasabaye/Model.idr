module Wasabaye.Model

import public Wasabaye.Env
import public Wasabaye.Effects.Dist
import public Wasabaye.Effects.ObsReader
import public Control.Eff

-- Model as a type-level function, specifying a program with two proofs of membership

public export
Model : (env : List (String, Type)) -> (es : List (Type -> Type)) -> (ret : Type) -> Type 
Model env es a = (Has Dist es, Has (ObsReader env) es) => Eff es a 

public export
runModel : (Has Dist es, Has (ObsReader env) es) => Model env es a -> Eff es a
runModel m = m

public export
handleCore : Env env -> Model env (Dist :: ObsReader env ::  es) a -> Eff (Observe :: Sample :: es) a
handleCore env = handleDist . handleObsRead env . runModel

exampleModel : {auto env : _} -> Model env es Int
exampleModel = pure 5

exampleHdlModel : Eff (Observe :: Sample :: []) Int
exampleHdlModel = handleCore ENil exampleModel

-- Smart constructors

public export
normal : Double -> Double -> (x : String) -> (prf : Observable env x Double) => Model env es Double
normal mu sigma x = do
  maybe_v <- send (Ask {prf} x)
  send (MkDist (Normal mu sigma) maybe_v)

public export
normal' : Double -> Double -> Model env es Double
normal' mu sigma = do
  send (MkDist (Normal mu sigma) Nothing)

