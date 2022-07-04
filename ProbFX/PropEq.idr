module ProbFX.PropEq

import Control.Function
import Data.Maybe
import Data.Either
import Data.Nat
import Data.List
import Data.List1
import Data.List1.Properties
import Data.List.Elem
import Data.These

||| Propositional equality interface
public export
interface PropEq t where
  propEq : (x1 : t) -> (x2 : t) -> Maybe (x1 = x2)

public export
PropEq () where
  propEq () () = Just Refl

public export
PropEq Bool where
  propEq True  True  = Just Refl
  propEq False False = Just Refl
  propEq False True  = Nothing
  propEq True  False = Nothing

public export
PropEq Nat where
  propEq Z     Z     = Just Refl
  propEq (S n) (S m) = cong S <$> propEq n m
  propEq Z     (S _) = Nothing
  propEq (S _) Z     = Nothing

public export
PropEq t => PropEq (Maybe t) where
  propEq Nothing Nothing = Just Refl
  propEq (Just x) (Just y) = cong Just <$> propEq x y
  propEq Nothing (Just _) = Nothing
  propEq (Just _) Nothing = Nothing

public export
(PropEq t, PropEq s) => PropEq (Either t s) where
  propEq (Left x)  (Left y)  = cong Left <$> propEq x y
  propEq (Right x) (Right y) = cong Right <$> propEq x y
  propEq (Left x) (Right y) = Nothing
  propEq (Right x) (Left y) = Nothing

public export
(PropEq a, PropEq b) => PropEq (a, b) where
  propEq (a, b) (a', b') = cong2 (,) <$> (propEq a a') <*> (propEq b b')

public export
PropEq a => PropEq (List a) where
  propEq [] [] = Just Refl
  propEq (x :: xs) [] = Nothing
  propEq [] (x :: xs) = Nothing
  propEq (x :: xs) (y :: ys) = cong2 (::) <$> (propEq x y) <*> (propEq xs ys)

public export
[FromEq] Eq a => PropEq a where
    propEq x y = case x == y of -- Blocks if x or y not concrete
                     True  => Just primitiveEq
                     False => Nothing
       where primitiveEq : forall x, y . x = y
             primitiveEq = believe_me (Refl {x})
             primitiveNotEq : forall x, y . Not (x = y)
             primitiveNotEq prf = believe_me {b = Void} ()

public export
PropEq Int where
    propEq = propEq @{FromEq}

public export
PropEq Bits8 where
    propEq = propEq @{FromEq}

public export
PropEq Bits16 where
    propEq = propEq @{FromEq}

public export
PropEq Bits32 where
    propEq = propEq @{FromEq}

public export
PropEq Bits64 where
    propEq = propEq @{FromEq}

public export
PropEq Int8 where
    propEq = propEq @{FromEq}

public export
PropEq Int16 where
    propEq = propEq @{FromEq}

public export
PropEq Int32 where
    propEq = propEq @{FromEq}

public export
PropEq Int64 where
    propEq = propEq @{FromEq}

public export
PropEq Char where
    propEq = propEq @{FromEq}

public export
PropEq Integer where
    propEq = propEq @{FromEq}

public export
PropEq String where
    propEq = propEq @{FromEq}


||| Some intentional code-smell is going on below.
export
PropEq Type where 
  propEq Int Int           = Just Refl
  propEq Double Double     = Just Refl
  propEq Bool Bool         = Just Refl
  propEq Nat Nat           = Just Refl
  propEq String String     = Just Refl
  propEq Char Char         = Just Refl
  propEq (List a) (List b) = cong List <$> propEq a b
  propEq (a, b) (a', b')   = cong2 (,) <$> propEq a a' <*> propEq b b'
  propEq _ _               = Nothing


||| PropEq version of `isElem`
export
isElem : PropEq a => (x : a) -> (xs : List a) -> Maybe (Elem x xs)
isElem x [] = Nothing
isElem x (y :: xs) with (propEq x y)
  isElem x (x :: xs) | Just Refl = Just Here
  isElem x (y :: xs) | Nothing with (isElem x xs)
    isElem x (y :: xs) | Nothing | Just xxs = Just (There xxs)
    isElem x (y :: xs) | Nothing | Nothing = Nothing
