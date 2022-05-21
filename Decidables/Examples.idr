module Decidables.Examples

import Data.Nat
import Data.Vect

-- | Equality type
infixr 8 :~:
data (:~:) : a -> b -> Type where
  Refl : x :~: x

cong : {f : t -> u} -> (p : a :~: b) -> (f a :~: f b)
cong Refl = Refl

-- | Example 1
checkEqNat : (n : Nat) -> (m : Nat) -> Maybe (n :~: m)
checkEqNat 0 0 = Just Refl
checkEqNat 0 (S k) = Nothing
checkEqNat (S k) 0 = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of 
                            Nothing => Nothing
                            Just p  => Just (cong {f = S} p)

-- | Example 2
myindex : Nat -> List a -> Maybe a
myindex _ Nil    = Nothing
myindex Z (x :: xs) = Just x
myindex (S k) (x :: xs) = myindex k xs 

sameElement : (n :~: m) -> ((myindex n xs) :~: (myindex m xs))
sameElement Refl = Refl

-- | Example 3
append : {n : Nat} -> Vect n a -> Vect m a -> Vect (n + m) a
append Nil ys       = ys
append ((::) x xs) ys = x :: (append xs ys)

samePlus : (1 + n = S n)
samePlus = Refl

f : (S n = 1 + n)
f = Refl

-- | Rewriting example.
myreverse : Vect n elem -> Vect n elem
myreverse Nil = Nil
myreverse {n = S k} (x :: xs) = let res = (myreverse xs) ++ [x]
                                in  rewrite plusCommutative 1 k in res -- Rewrite type '1 + k', which by definition normalises to 'S k', to the type 'k + 1'.

-- plusCommutative : (left, right : Nat) -> left + right = right + left
