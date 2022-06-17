module Wasabaye.Effects.ObsReader

import Data.List
import Data.List.Elem
import Wasabaye.Env
import Wasabaye.Prog

public export
Observable : (env : List (String, Type)) -> (var : String) -> (var_type : Type) -> Type
Observable env x a = Elem (x, a) env

public export
Observables : (env : List (String, Type)) -> (var : List String) -> (var_type : Type) -> Type
Observables env (x :: xs) a = (Elem (x, a) env, Observables env xs a)
Observables env [] a        = ()

public export
data ObsReader : (env : List (String, Type)) -> Effect where 
  Ask : (x : String) -> (prf : Observable env x a) => ObsReader env (Maybe a)

defaultTail : List a -> List a
defaultTail [] = []
defaultTail (x :: xs) = xs 

public export
handleObsRead : (prf : Elem (ObsReader env) es) => Env env -> Prog es a -> Prog (es - ObsReader env) a
handleObsRead env (Val x)  = pure x
handleObsRead env (Op op k) = case discharge op {prf} of
    Left op' => Op op' (handleObsRead env . k)
    Right (Ask x) => do
        let vs      = get x env 
            maybe_v = head' vs 
            env'    = set x (defaultTail vs) env 
        handleObsRead env' (k maybe_v)