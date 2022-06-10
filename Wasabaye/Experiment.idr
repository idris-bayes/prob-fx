import Control.Eff

-- data AtIndex : a -> List a -> Nat -> Type where
--   Z : AtIndex a (a :: as) Z
--   S : AtIndex a as n -> AtIndex a (b :: as) (S n)

-- data NonEmpty : List a -> Type where
--   IsNonEmpty : NonEmpty (x :: xs)

-- data Union : (es : List (Type -> Type)) -> Type -> Type where
--   MkUnion : {auto ok : NonEmpty es} 
--         -> (AtIndex e es k) 
--         -> e x 
--         -> Union es x

-- partial
-- discharge :  Union (e :: es) x    -- if Left, then 'es' must be non-empty. If Right, then 'es' is not necessarily non-empty.
--           -> Either (Union es x) (e x)
-- discharge (MkUnion  Z t)         = Right t
-- -- discharge (MkUnion (S k) t) = Left (MkUnion   k t)

-- data Id : a -> Type where
--   MkId : a -> Id a

-- data IdB : a -> Type where
--   MkIdB : a -> IdB a

{-
This question has some flaws in it, but it's purely for learning purposes. I have an open union type, Union es x, whose constructor specifies a type 'e x' where 'e' is an element of 'es'. 

I then have a function discharge that either 1) matches on 'e x', or 2) removes e from the front of the 'e :: es'.  The second case complains that we don't know if 'es' is NonEmpty: how can I express that matching on Left  (without taking advantage of AtIndex)? I tried something alone the lines:

 discharge' :  Union (e :: es) x
           -> Either ({auto ok : NonEmpty es} -> Union es x) (e x)

 But this runs into problems.
-}

data RowReader : Type -> Type -> Type where

-- data ReaderProg : (env : List (String, Type)) -> (es : List (Type -> Type)) -> Type -> Type where
--   MkReaderProg : Has (RowReader env) es => Eff es a -> ReaderProg env es a

ReaderProg : (env : Type) -> (es : List (Type -> Type)) -> (a : Type) -> Type
ReaderProg env es a = Has (RowReader env) es => Eff es a

handleRowReader : Eff (RowReader e :: es) a -> e -> Eff es a

prog : {env : _} -> Has (RowReader env) es => Eff es Int
prog = pure 5 

runProg : Eff es Int
runProg = handleRowReader (prog {env = Integer}) 5


-- Functor (Model es) where
--   map f (MkModel prog) = MkModel (map f prog)

-- Applicative (Model es) where
--   (MkModel f) <*> (MkModel a) = MkModel (f <*> a)
--   pure x = MkModel (pure x)
