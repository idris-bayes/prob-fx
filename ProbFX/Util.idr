module ProbFX.Util

import Data.List
import Data.Vect

namespace List
  export
  maybeIndex : Nat -> List a -> Maybe a
  maybeIndex i xs with (inBounds i xs)
    _ | Yes prf = Just (index i xs)
    _ | No  _   = Nothing

  export
  defaultTail : List a -> List a
  defaultTail [] = []
  defaultTail (x :: xs) = xs

  export
  replicateM : Monad m => Nat -> m a -> m (List a)
  replicateM n = sequence . replicate n

  export
  mapM : Monad m => (a -> m b) -> List a -> m (List b)
  mapM f = sequence . map f

  export
  insert : Eq a => a -> b -> List (a, b) -> List (a, b)
  insert k' v' [] = [(k', v')]
  insert k' v' ((k, v) :: kvs) = if k == k' then ((k', v') :: kvs) else (k, v) :: insert k' v' kvs

namespace Vect
  export
  replicateM : Monad m => (n : Nat) -> m a -> m (Vect n a)
  replicateM n = sequence . replicate n

export
roundUp16 : Nat -> Nat
roundUp16 n = n + (minus 16 (n `mod` 16))

export
toSeed : Double -> Bits64
toSeed = cast
