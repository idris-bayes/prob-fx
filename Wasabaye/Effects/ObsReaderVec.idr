module Wasabaye.Effects.ObsReaderVec

import Data.List
import Data.List.Elem
import Wasabaye.EnvVec
import Wasabaye.Prog


-- public export
-- Observables : (env : List (String, Type)) -> (var : List String) -> (var_type : Type) -> Type
-- Observables env (x :: xs) a = (Elem (x, a) env, Observables env xs a)
-- Observables env [] a        = ()

public export
data ObsReader : (env : List (String, Nat,  Type)) -> Effect where 
  Ask : (x : String) -> (obs_prf : ObservableV env x n a) => ObsReader env (Maybe a)

defaultTail : List a -> List a
defaultTail [] = []
defaultTail (x :: xs) = xs 

public export
handleObsRead : (prf : Elem (ObsReader env) es) => Env env -> Prog es a -> Prog (es - ObsReader env) a
handleObsRead env (Val x)  = pure x
handleObsRead env (Op op k) = case discharge op {prf} of
    Left op' => Op op' (handleObsRead env . k)
    Right (Ask x {obs_prf} ) => do
        let vs      = get {prf=obs_prf} x env 
            maybe_v = head'  vs 
            env'    = set {prf=obs_prf} x (defaultTail vs) env 
        handleObsRead env' (k maybe_v)