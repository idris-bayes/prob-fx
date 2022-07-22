module ProbFX.Inference.MH

import ProbFX.Effects.Dist
import ProbFX.PrimDist
import ProbFX.Prog
import Data.List.Elem
import Data.SortedSet
import Data.SortedMap
import Data.Maybe

||| Trace of sampled values
{-
Looks like recording the types of sampled values will be too much of a pain.
Best to work with traces of random doubles between 0 and 1, like monad bayes does.
-}
public export
STrace : Type
STrace = SortedMap Addr Double

||| Handler for recording samples
handleSamp : (prf : Elem Sample es) => STrace -> Prog es a -> Prog es (a, STrace)

-- traceSamples' strace (Val x) = pure (x, strace)
-- traceSamples' strace (Op op k) with (prj op {prf})
--   _ | Just (MkSample d addr)
--         = do  y <- call (MkSample d addr)
--               let prim_val  = toPrimVal d y
--                   strace'   = SortedMap.insert addr (Erase d, prim_val) strace
--               (traceSamples' strace' . k) y
--   _ | Nothing = Op op (traceSamples' strace . k)

-- public export
-- traceSamples : (prf : Elem Sample es) => Prog es a -> Prog es (a, STrace)
-- traceSamples = traceSamples' SortedMap.empty

-- accept :
--      Addr               -- ^ proposal sample address
--   -> (STrace, LPTrace)  -- ^ previous sample and log-prob traces
--   -> (STrace, LPTrace)  -- ^ new sample and log-prob traces
--   -> Double
-- accept x0 (strace, lptrace) (strace', lptrace') =
--   let s_addrs  = keySet strace
--       s_addrs' = keySet strace'
--       dom_log  = log (cast $ length $ SortedSet.toList s_addrs) - log (cast $ length $ SortedSet.toList s_addrs')
--       sampled  = singleton x0 `union` (s_addrs  `difference` s_addrs')
--       sampled' = singleton x0 `union` (s_addrs' `difference` s_addrs)
--       logα     = foldl (\logα, k => logα + fromMaybe 0 (lookup k lptrace))
--                         0 (keySet lptrace `difference` sampled)
--       logα'    = foldl (\logα, k => logα + fromMaybe 0 (lookup k lptrace'))
--                         0 (keySet lptrace' `difference` sampled')
--   in  exp (dom_log + logα' - logα)

{-
Looks like recording the types of sampled values will be too much of a pain.
Best to work with traces of random doubles between 0 and 1, like monad bayes does.
-}


-- ||| Trace of log probabilities
-- public export
-- LPTrace : Type
-- LPTrace = SortedMap Addr Double

-- export
-- ||| Handler for recording log-probabilities
-- traceLogProbs' : (prfS : Elem Sample es) => (prfO : Elem Observe es) => LPTrace -> Prog es a -> Prog es (a, LPTrace)
-- traceLogProbs' lptrace (Val x) = pure (x, lptrace)
-- traceLogProbs' lptrace (Op op k) with (prj op {prf=prfS})
--   _ | Just (MkSample d tag)
--         = do  y <- call (MkSample d tag)
--               let lptrace' = SortedMap.insert tag (logProb d y) lptrace
--               (traceLogProbs' lptrace' . k) y
--   _ | Nothing with (prj op {prf=prfO})
--     _ | Just (MkObserve d y tag)
--           = do  y <- call (MkObserve d y tag)
--                 let lptrace' = SortedMap.insert tag (logProb d y) lptrace
--                 (traceLogProbs' lptrace' . k) y
--     _ | _ = Op op (traceLogProbs' lptrace . k)

-- public export
-- traceLogProbs : (prfS : Elem Sample es) => (prfO : Elem Observe es) => Prog es a -> Prog es (a, LPTrace)
-- traceLogProbs = traceLogProbs' SortedMap.empty

-- ||| Get trace size
-- public export
-- traceSize : List (a, List b) -> Nat
-- traceSize [] = 0
-- traceSize ((_, xs) :: rest) = length xs + traceSize rest

-- lookupSample : Addr -> PrimDist a -> STrace -> Maybe a
-- lookupSample addr d strace = do
--   (Erase d', prim_val) <- lookup addr strace
--   let b = d ~=~ d'
--   ?h
