||| The effects for primitive distributions, sampling, and observing
module ProbFX.Effects.Dist

import Data.List
import Data.Maybe
import Statistics.Distribution.Binomial
import Statistics.Distribution.Normal
import Statistics.Distribution.Uniform
import ProbFX.Prog
import ProbFX.PrimDist
import System.Random
import ProbFX.Util

||| Distribution effect
public export
record Dist (a : Type) where
  constructor MkDist
  ||| Underlying primitive distribution
  dist : PrimDist a
  ||| Optional observed value
  obs  : Maybe a
  ||| Random variable name
  tag  : String

||| An address is a run-time identifier for a probabilistic operation
||| comprised of the random variable name and its run-time occurrence
public export
Addr : Type
Addr = (String, Nat)

||| Observe effect
public export
data Observe : Effect where
  ||| The single operation of the Observe effect
  ||| @ dist the underlying primitive distribution to condition against
  ||| @ obs  the observed value
  ||| @ addr the address
  MkObserve  : (dist : PrimDist a)
            -> (obs : a)
            -> (addr : Addr)
            -> Observe a

||| Sample effect
public export
data Sample : Effect where
  ||| The single operation of the Sample effect
  ||| @ dist the underlying primitive distribution to sample from
  ||| @ addr the address
  MkSample : (dist : PrimDist a)
          -> (addr : Addr)
          -> Sample a

||| Handle Dist to Sample or Observe, and assign an address
public export
handleDist : (prf : Elem Dist es) => Prog es a -> Prog (Observe :: Sample :: es - Dist) a
handleDist = loop "" []
  where
    loop : String -> List (String, Nat) -> Prog es a -> Prog (Observe :: Sample :: es - Dist) a
    loop _ _ (Val x) = pure x
    loop prevTag tagMap (Op op k) =
      case discharge op {prf} of
        Right d =>  let tag    = d.tag
                        tagIdx = let currentIdx = fromMaybe 0 (lookup tag tagMap)
                                in  if tag /= prevTag then roundUp16 currentIdx else currentIdx
                        tagMap' = insert tag (tagIdx + 1) tagMap
                    in  case d.obs of Just y  => do v <- call (MkObserve d.dist y (tag, tagIdx))
                                                    (loop tag tagMap' . k) v
                                      Nothing => do v <- call (MkSample d.dist (tag, tagIdx))
                                                    (loop tag tagMap'  . k) v
        Left op' => Op (weaken1 $ weaken1 op') (loop prevTag tagMap  . k)
