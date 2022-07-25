module ProbFX.Effects.ObsRW

import Data.List
import Data.So
import Data.List.Elem
import ProbFX.Env
import ProbFX.Prog
import ProbFX.Util

||| Reading and writing to model environments
public export
data ObsRW : (env : List (String, Type)) -> Effect where
  Read  : (x : String) -> (prf : Observable env x a) => ObsRW env (Maybe a)
  Write : (x : String) -> (val : a) -> (prf : Observable env x a) => ObsRW env ()

export
handleObsRW : (prf : Elem (ObsRW env) es) => Env env -> Prog es a -> Prog (es - ObsRW env) (a, Env env)
handleObsRW env_in prog = loop env_in emptyEnv prog
  where
    loop : Env env -> Env env -> Prog es a -> Prog (es - ObsRW env) (a, Env env)
    loop env_in env_out (Val x)   = pure (x, env_out)
    loop env_in env_out (Op op k) = case discharge op {prf} of
        Left op'       => Op op' (loop env_in env_out . k)
        Right (Read x) => do
            let vs      = get x env_in
                maybe_v = head' vs
                env_in' = set x (defaultTail vs) env_in
            loop env_in' env_out (k maybe_v)
        Right (Write x v) => do
            let vs       = get x env_out
                vs'      = v :: vs
                env_out' = set x vs' env_out
            loop env_in env_out' (k ())