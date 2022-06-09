module Effects.ObsReader

import Data.List.Elem
import Env
import Prog

Observable : (env : List (String, Type)) -> (var : String) -> (var_type : Type) -> Type
Observable env x a = Elem (x, a) env

data ObsReader : (env : List (String, Type)) -> (ret : Type) -> Type where 
  Ask : (prf : Observable env x a) => ObsReader env (Maybe a)

partial
handleObsRead : Env env -> Prog (ObsReader env :: es) a -> Prog es a
handleObsRead env (Val a) = Val a
handleObsRead env (Op op k) with (discharge op)
  _ | Left (op', _) = Op op' (handleObsRead env . k)
--   _ | Left op' = Op (weaken_op $ weaken_op op') (handleDist . k)
--   _ | Right d = case d.obs of Just y  => do x <- call (MkObserve d.dist y) 
--                                             (handleDist . k) x
--                               Nothing => call (MkSample d.dist) >>= (handleDist . k)
