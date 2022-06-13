module Wasabaye.Effects.ObsReader

import Data.List
import public Data.List.Elem
import Wasabaye.Env
import Control.Eff

public export
Observable : (env : List (String, Type)) -> (var : String) -> (var_type : Type) -> Type
Observable env x a = Elem (x, a) env

public export
data ObsReader : (env : List (String, Type)) -> (ret : Type) -> Type where 
  Ask : (x : String) -> (prf : Observable env x a) => ObsReader env (Maybe a)

-- Eff version
public export
handleObsRead : (prf : Has (ObsReader env) es) => Env env -> Eff es a -> Eff (es - ObsReader env) a
handleObsRead env prog = case toView prog of
  Pure x    => pure x
  Bind op k => case decomp op {prf} of
    Left op' => fromView $ Bind op' (handleObsRead env . k)
    Right (Ask x) => do
        let vs      = get x env 
            maybe_v = head' vs 
            env'    = set x (defaultTail vs) env 
        handleObsRead env' (k maybe_v)