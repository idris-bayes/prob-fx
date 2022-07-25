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
  dist : PrimDist a
  obs  : Maybe a
  tag  : String

||| Address
public export
Addr : Type
Addr = (String, Nat)

||| Observe effect
public export
data Observe : Effect where
  MkObserve : PrimDist a -> a -> Addr -> Observe a

||| Sample effect
public export
data Sample : Effect where
  MkSample  : PrimDist a -> Addr -> Sample a

||| Handle the Dist effect to a Sample or Observe effect and assign an address
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
