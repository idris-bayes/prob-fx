module ProbFX.Old.UniqueList

import Data.List.Elem
import Decidable.Equality

public export
data NotElem : (x : a) -> (xs : List a) -> Type where
  NotAnywhere : NotElem x Nil
  NotHere     : (contra : x === y -> Void) -> NotElem x xs -> NotElem x (y :: xs)

atHead : (x === y) -> (NotElem x (y :: xs) -> Void)
atHead Refl NotAnywhere impossible
atHead Refl (NotHere contra _) = contra Refl

isElem_cons : (NotElem x xs -> Void) -> (NotElem x (y :: xs) -> Void)
isElem_cons inTail (NotHere notInHead notInTail) = inTail notInTail 

notElem : DecEq a => (x : a) -> (xs : List a) -> Dec (NotElem x xs)
notElem x [] = Yes NotAnywhere
notElem x (y :: xs) with (decEq x y)
  _ | Yes eq = No (atHead eq)
  _ | No neq with (notElem x xs) 
    _ | Yes prf = Yes (NotHere neq prf)
    _ | No contra = No (isElem_cons contra)

data UList : List a -> Type where
  UNil  : UList []
  UCons : (x : a) -> UList xs -> {auto prf : NotElem x xs} -> UList (x :: xs)

consPrf : (x : a) -> UList xs -> {auto prf : NotElem x xs} -> UList (x :: xs)
consPrf x xs = UCons x xs


f : (1 === 2 -> Void)
f Refl impossible

exampleUList : UList [1, 2]
exampleUList = UCons 1 (UCons 2 UNil) {prf = NotHere f NotAnywhere}