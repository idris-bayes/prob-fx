module ProbFX.Inference.MH

import ProbFX.Trace
import ProbFX.Effects.Dist
import ProbFX.PrimDist
import Data.SortedSet
import Data.SortedMap
import Data.Maybe

lookupSample : Addr -> PrimDist a -> STrace -> Maybe a
lookupSample addr d strace = do
  (Erase d', prim_val) <- lookup addr strace
  let b = d ~=~ d'
  ?h

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

{-
Looks like recording the types of sampled values will be too much of a pain.
Best to work with traces of random doubles between 0 and 1, like monad bayes does.
-}