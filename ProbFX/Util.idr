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

namespace Vect
  export
  replicateM : Monad m => (n : Nat) -> m a -> m (Vect n a)
  replicateM n = sequence . replicate n
