module Data.List.NonEmpty

public export
data NonEmpty : List a -> Type where
  IsNonEmpty : NonEmpty (x :: xs)
