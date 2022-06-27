module Wasabaye.Effects.Trace

import Wasabaye.Prog
import Wasabaye.PrimDist
import Wasabaye.Effects.Dist

public export
partial
traceSamples : (prf : Elem Sample es) => Trace -> Prog es a -> Prog es a
traceSamples strace (Val x) = pure x 
traceSamples strace (Op op k) = case prj op {prf} of
  Just (MkSample d x) => do y <- send (MkSample d x) 
                            (traceSamples strace . k) y
  --                          Nothing => send (MkSample d.dist d.tag) >>= (handleDist . k)
  Nothing => Op op (traceSamples strace . k)
