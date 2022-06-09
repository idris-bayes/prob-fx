module Wasabaye.Model

import Wasabaye.Env
import Wasabaye.Prog
import Wasabaye.Effects.Dist
import Wasabaye.Effects.ObsReader

-- handleCore : {es : _} 
--   -> Env env -> Prog (ObsReader env :: Dist :: es) a -> Prog (Observe :: Sample :: es) a
-- handleCore env = handleDist . handleObsRead env 

-- Model : (env : List (String, Type)) -> (effs : List (Type -> Type)) -> (ret : Type) -> Type
-- Model env es a = (Member Dist es, Member (ObsReader env) es) => Prog es a

-- m3 : {auto env : _} -> Model env es a

-- f3 : {es : _} -> Prog (Observe :: Sample :: es) a
-- f3 = handleCore ENil m3

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

progModel : Model env es a 

handleCore : {es : _} 
  -> Env env -> Model env (ObsReader env :: Dist :: es) a -> Prog (Observe :: Sample :: es) a
handleCore env (MkModel prog) = handleDist (handleObsRead env prog)

f3 : {es : _} -> Prog (Observe :: Sample :: es) a
f3 = handleCore ENil progModel

-- While processing right hand side of f. Can't find an implementation for 
-- (Member Dist (ObsReader [] :: (Dist :: es)), Member (ObsReader ?env) (ObsReader [] :: (Dist :: es))).