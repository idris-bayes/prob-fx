module Wasabaye.Model

import Wasabaye.Env
import Wasabaye.Prog
import Wasabaye.Effects.Dist
import Wasabaye.Effects.ObsReader

data Model : (env : List (String, Type)) -> (es : List (Type -> Type)) -> (ret : Type) -> Type where
  MkModel :  (Member Dist es, Member (ObsReader env) es) => Prog es a -> Model env es a

runModel : Model env es a -> Prog es a
runModel (MkModel prog) = prog

progDist : (Member Dist es) => Prog es Int
progDist = Val 5

f1 : {es : _} -> Prog (Observe :: Sample :: es) Int
f1 = handleDist progDist

progReader : {auto env : _} -> (Member (ObsReader env) es) => Prog es Int
progReader = Val 5

f2 : {es : _} -> Prog es Int
f2 = handleObsRead ENil progReader

progModel : Model env es Int
-- progModel = MkModel $ Val 5

handleCore : {es : _} 
  -> Env env -> Model env (ObsReader env :: Dist :: es) a -> Prog (Observe :: Sample :: es) a
handleCore env = handleDist . handleObsRead env . runModel

f3 : {es : _} -> Prog (Observe :: Sample :: es) Int
f3 = handleCore ENil progModel

