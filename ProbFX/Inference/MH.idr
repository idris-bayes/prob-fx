module ProbFX.Inference.MH

import ProbFX.Trace
import ProbFX.Effects.Dist
import Data.SortedSet
import Data.SortedMap
import Data.Maybe

accept :
     Addr               -- ^ proposal sample address
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