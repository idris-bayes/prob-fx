module Wasabaye.Effects.ObsReader

import Data.List
import Data.List.Elem
import Wasabaye.Env
import Wasabaye.Prog

public export
Observable : (env : List (String, Type)) -> (var : String) -> (var_type : Type) -> Type
Observable env x a = Elem (x, a) env

public export
data ObsReader : (env : List (String, Type)) -> (ret : Type) -> Type where 
  Ask : (x : String) -> (prf : Observable env x a) => ObsReader env (Maybe a)

public export
handleObsRead : Env env -> Prog (ObsReader env :: es) a -> Prog es a
handleObsRead env (Val a) = Val a
handleObsRead env (Op op k) with (discharge op)
  _ | Left (op', _) = Op op' (handleObsRead env . k)
  _ | Right (Ask x {prf}) = do
        let vs      = get x env {prf}
            maybe_v = head' vs 
            env'    = set x (defaultTail vs) env {prf}
        handleObsRead env' (k maybe_v)