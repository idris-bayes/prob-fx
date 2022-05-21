module Data.List.AtIndex

import Data.DPair
import Data.Nat
import Decidable.Equality

%default total

||| @AtIndex witnesses the fact that a natural number encodes a membership proof.
||| It is meant to be used as a runtime-irrelevant gadget to guarantee that the
||| natural number is indeed a valid index.
public export
data AtIndex : a -> List a -> Nat -> Type where
  Z : AtIndex a (a :: as) Z
  S : AtIndex a as n -> AtIndex a (b :: as) (S n)

||| Inversion principle for Z constructor
export
inverseZ : AtIndex x (y :: xs) Z -> x === y
inverseZ Z = Refl

||| inversion principle for S constructor
export
inverseS : AtIndex x (y :: xs) (S n) -> AtIndex x xs n
inverseS (S p) = p

||| An empty list cannot possibly have members
export
Uninhabited (AtIndex a [] n) where
  uninhabited Z impossible
  uninhabited (S _) impossible

||| For a given list and a given index, there is only one possible value
||| stored at that index in that list
export
atIndexUnique : AtIndex a as n -> AtIndex b as n -> a === b
atIndexUnique Z Z = Refl
atIndexUnique (S p) (S q) = atIndexUnique p q
 
||| If the equality is not decidable, we may instead rely on interface resolution
public export
interface FindElement (0 t : a) (0 ts : List a) where
  findElement : Subset Nat (AtIndex t ts)

FindElement t (t :: ts) where
  findElement = Element 0 Z

FindElement t ts => FindElement t (u :: ts) where
  findElement = let (Element n prf) = findElement in
                Element (S n) (S prf)

||| Given an index, we can decide whether there is a value corresponding to it
public export
lookup : (n : Nat) -> (xs : List a) -> Dec (Subset a (\ x => AtIndex x xs n))
lookup n [] = No (\ p => void (absurd (snd p)))
lookup Z (x :: xs) = Yes (Element x Z)
lookup (S n) (x :: xs) = case lookup n xs of
  Yes (Element x p) => Yes (Element x (S p))
  No notInxs => No (\ (Element x p) => void (notInxs (Element x (inverseS p))))

||| An AtIndex proof implies that n is less than the length of the list indexed into
public export
inRange : (n : Nat) -> (xs : List a) -> (0 _ : AtIndex x xs n) -> LTE n (length xs)
inRange n [] p = void (absurd p)
inRange Z (x :: xs) p = LTEZero
inRange (S n) (x :: xs) p = LTESucc (inRange n xs (inverseS p))

|||
export
weakenR : AtIndex x xs n -> AtIndex x (xs ++ ys) n
weakenR Z = Z
weakenR (S p) = S (weakenR p)
