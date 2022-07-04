module ProbFX.Util

import Data.List

export
maybeIndex : Nat -> List a -> Maybe a
maybeIndex i xs with (inBounds i xs)
  _ | Yes prf = Just (index i xs)
  _ | No  _   = Nothing

export
defaultTail : List a -> List a
defaultTail [] = []
defaultTail (x :: xs) = xs 
