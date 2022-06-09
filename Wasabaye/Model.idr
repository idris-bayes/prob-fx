module Wasabaye.Model

import Wasabaye.Env
import Wasabaye.Prog
import Wasabaye.Effects.Dist
import Wasabaye.Effects.ObsReader

Model : (env : List (String, Type)) -> (effs : List (Type -> Type)) -> (ret : Type) -> Type
Model env es a = (Member Dist es, Member (ObsReader env) es) => Prog es a

handleCore : {es : _} 
  -> Env env -> Prog (ObsReader env :: Dist :: es) a -> Prog (Observe :: Sample :: es) a
handleCore env = handleDist . handleObsRead env 


m1 : (Member Dist es) => Prog es Int
m1 = Val 5

f1 : {es : _} -> Prog (Observe :: Sample :: es) Int
f1 = handleDist m1

m2 : {auto env : _} -> (Member (ObsReader env) es) => Prog es Int
m2 = Val 5

f2 : {es : _} -> Prog es Int
f2 = handleObsRead ENil m2

m3 : {auto env : _} -> Model env es a

f3 : {es : _} -> Prog (Observe :: Sample :: es) a
f3 = handleCore ENil m3


-- While processing right hand side of f. Can't find an implementation for 
-- (Member Dist (ObsReader [] :: (Dist :: es)), Member (ObsReader ?env) (ObsReader [] :: (Dist :: es))).