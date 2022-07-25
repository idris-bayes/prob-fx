module ProbFX.Inference.MH

import ProbFX.Effects.Dist
import ProbFX.PrimDist
import ProbFX.Prog
import ProbFX.Sampler
import Data.List1
import Data.List.Elem
import Data.SortedSet
import Data.SortedMap
import Data.Vect
import Data.Maybe

||| Trace of sampled values
{-
Looks like recording the types of sampled values will be too much of a pain.
Best to work with traces of random doubles between 0 and 1, like monad bayes does.
-}
public export
STrace : Type
STrace = SortedMap Addr Double

public export
LPTrace : Type
LPTrace = SortedMap Addr Double

export
accept
   : Addr               -- ^ proposal sample address
  -> (STrace, LPTrace)  -- ^ previous sample and log-prob traces
  -> (STrace, LPTrace)  -- ^ new sample and log-prob traces
  -> Double
accept x0 (strace, lptrace) (strace', lptrace') =
  let s_addrs  = keySet strace
      s_addrs' = keySet strace'
      dom_log  = log (cast $ length $ SortedSet.toList s_addrs) - log (cast $ length $ SortedSet.toList s_addrs')
      sampled  = singleton x0 `union` (s_addrs  `difference` s_addrs')
      sampled' = singleton x0 `union` (s_addrs' `difference` s_addrs)
      logα     = foldl (\logα, k => logα + fromMaybe 0 (lookup k lptrace))
                        0 (keySet lptrace `difference` sampled)
      logα'    = foldl (\logα, k => logα + fromMaybe 0 (lookup k lptrace'))
                        0 (keySet lptrace' `difference` sampled')
  in  exp (dom_log + logα' - logα)

||| Handler for reusing samples (and generating new ones when necessary)
export
handleSample : STrace -> Prog [Sample] a -> Sampler (a, STrace)
handleSample strace (Val x)   = pure (x, strace)
handleSample strace (Op op k) with (prj1 op)
  _ | (MkSample d addr) with (lookup addr strace)
    _ | Just r  = do sample d r >>= (handleSample strace . k)
    _ | Nothing = do r <- random
                     sample d r >>= (handleSample (insert addr r strace) . k)

||| Handler for recording log-probabilities
export
handleObserve : Elem Observe es => Prog es a -> Prog (es - Observe) (a, LPTrace)
handleObserve = loop empty
  where
    loop : LPTrace -> Prog es a -> Prog (es - Observe) (a, LPTrace)
    loop lptrace (Val x)   = pure (x, lptrace)
    loop lptrace (Op op k) = case discharge op of
      Left op'                   => Op op' (loop lptrace . k)
      Right (MkObserve d y addr) => loop (insert addr (logProb d y) lptrace) (k y)

||| Handler for one program execution under MH
export
runMH : STrace -> Prog [Observe, Sample] a -> Sampler ((a, LPTrace), STrace)
runMH strace = handleSample strace . handleObserve

||| Perform one iteration of MH
export
mhStep
   : Prog [Observe, Sample] a
  -> List1 ((a, LPTrace), STrace)            -- ^ trace of previous MH results
  -> Sampler (List1 ((a, LPTrace), STrace))  -- ^ updated trace of MH results
mhStep prog trace = do
  let ((a, lptrace), strace) = head trace
      addrs : List Addr
      addrs = keys strace
      uniform_addrs : PrimDist Addr
      uniform_addrs = Discrete $ Vect.fromList $ (("", 0), 0.0) :: (map (, 1.0 / cast (length addrs)) addrs)

  sample_site               <- sample uniform_addrs !random
  ((a', lptrace'), strace') <- runMH (insert sample_site !random strace) prog
  ?hole
