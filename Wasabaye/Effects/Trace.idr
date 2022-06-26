module Wasabaye.Effects.Trace

import Data.List
import Data.List.Elem
import Wasabaye.Env
import Wasabaye.Prog
import Wasabaye.Effects.ObsReader
import Wasabaye.Effects.Dist


traceSamples : (prf : Elem Dist es) =>  Prog es a -> Prog es a
traceSamples (Val x)  = pure x
traceSamples (Op op k) = case prj op {prf} of
  Nothing                     => (Op op (traceSamples . k))
  Just (MkDist d maybe_y tag) => ?hole1


    -- Left op' => Op op' (handleObsRead env . k)
    -- Right (Ask x) => do
    --     let vs      = get x env 
    --         maybe_v = head' vs 
    --         env'    = set x (defaultTail vs) env 
    --     handleObsRead env' (k maybe_v)
