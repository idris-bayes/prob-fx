||| Metropolis-Hastings inference
module ProbFX.Inference.MH

import ProbFX.Effects.Dist
import ProbFX.PrimDist
import ProbFX.Prog
import ProbFX.Model
import ProbFX.Sampler
import Data.List1
import Data.List.Elem
import Data.SortedSet
import Data.SortedMap
import Data.Vect
import Data.Maybe

||| Trace of sampled values
public export
STrace : Type
STrace = SortedMap Addr Double

||| Trace of log-probabilities
public export
LPTrace : Type
LPTrace = SortedMap Addr Double

||| Compute an accept ratio using the previous MH result and the newly proposed MH result
export
accept
   : Addr               -- ^ proposal sample address
  -> (STrace, LPTrace)  -- ^ previous sample and log-prob traces
  -> (STrace, LPTrace)  -- ^ new sample and log-prob traces
  -> Double             -- ^ acceptance ratio
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
  in  min 1.0 (exp (dom_log + logα' - logα))

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
handleMH : STrace -> Prog [Observe, Sample] a -> Sampler ((a, LPTrace), STrace)
handleMH strace = handleSample strace . handleObserve

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
      sample_sites : PrimDist Addr
      sample_sites = Discrete $ Vect.fromList $ (("", 0), 0.0) :: (map (, 1.0 / cast (length addrs)) addrs)

  x0  <- sample sample_sites !random
  ((a', lptrace'), strace') <- handleMH (insert x0 !random strace) prog

  let accept_ratio = accept x0 (strace, lptrace) (strace', lptrace')
  pure $ if accept_ratio > !random
          then ((a', lptrace'), strace') ::: List1.forget trace
          else trace

||| Perform MH for n iterations
export
mhInternal
   : Nat                                    -- ^ number of MH iterations
  -> Prog [Observe, Sample] a
  -> Sampler (List ((a, LPTrace), STrace))  -- ^ trace of MH results
mhInternal n prog = do
  mh_out_0 <- handleMH SortedMap.empty prog
  List1.forget <$> foldl (>=>) pure (replicate n (mhStep prog)) (mh_out_0 ::: [])

||| Top-level wrapper for MH on a model
export
mh : Nat                          -- ^ number of MH iterations
  -> Model env [] a               -- ^ model
  -> Env env                      -- ^ input model environment
  -> Sampler (List (Env env))     -- ^ output model environments
mh n model env_in = do
  let prog : Prog [Observe, Sample] (a, Env env)
      prog = handleCore env_in model
  mh_trace <- mhInternal n prog
  pure (map (snd . fst . fst) mh_trace)