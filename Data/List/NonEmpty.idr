module Data.List.NonEmpty

public export
data NonEmpty : List a -> Type where
  IsNonEmpty : NonEmpty (x :: xs)

-- export
-- nonEmpty_cons : NonEmpty xs -> NonEmpty (x :: xs)
-- nonEmpty_cons p = IsNonEmpty 
