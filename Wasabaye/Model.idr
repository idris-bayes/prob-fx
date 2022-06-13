module Wasabaye.Model

import Wasabaye.Env
import Wasabaye.Effects.Dist
import Wasabaye.Effects.ObsReader
import Control.Eff

-- Model as a type-level function, specifying a program with two proofs of membership

Model : (env : List (String, Type)) -> (es : List (Type -> Type)) -> (ret : Type) -> Type 
Model env es a = (Has Dist es, Has (ObsReader env) es) => Eff es a 

runModel : (Has Dist es, Has (ObsReader env) es) => Model env es a -> Eff es a
runModel m = m

handleCore : Env env -> Model env (Dist :: ObsReader env ::  es) a -> Eff (Observe :: Sample :: es) a
handleCore env = handleDist . handleObsRead env . runModel

exampleModel : {auto env : _} -> Model env es Int
exampleModel = pure 5

exampleHdlModel : Eff (Observe :: Sample :: []) Int
exampleHdlModel = handleCore ENil exampleModel

-- Smart constructors

normal : Double -> Double -> (x : String) -> (prf : Observable env x Double) => Model env es Double
normal mu sigma x = do
  maybe_v <- send (Ask {prf} x)
  send (MkDist (Normal mu sigma) maybe_v)

normal' : Double -> Double -> Model env es Double
normal' mu sigma = do
  send (MkDist (Normal mu sigma) Nothing)

