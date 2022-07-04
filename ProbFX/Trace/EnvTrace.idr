module ProbFX.Trace.EnvTrace

import Data.List.Elem
import ProbFX.Env
import ProbFX.PropEq

||| Using model environments as Traces

||| A sample trace that only contains variables that are "named" by the user
STrace : (env : List (String, Type)) -> Type
STrace = Env 

||| A log-probability trace that only contains variables that are "named" by the user
LPTrace : (env : List (String, Type)) -> Type
LPTrace = Env . map (map (const Double))

||| Attempt to look up the trace of an observable variable of a particular type
export
lookup : {env : _} -> PropEq a => (x : String) -> (a : Type) -> Env env -> Maybe (List a)  
lookup x a xas with (PropEq.isElem (x, a) env)
  _ | Just prf = Just (get x xas {prf})
  _ | Nothing  = Nothing
