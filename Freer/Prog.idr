module Freer.Prog 

import Freer.EffectSum
import Data.List.NonEmpty

data Prog : (es : List (Type -> Type)) -> (a : Type) -> Type where
  Op  : {auto ok : NonEmpty es} -> (op : EffectSum es x) -> (k : x -> Prog es a) -> Prog es a
  Val : a -> Prog es a
 
Functor (Prog es) where
  map f (Op op k) = Op op (map f . k)
  map f (Val a)   = Val (f a)

Applicative (Prog es) where
  pure = Val
  Op op k <*> p = Op op (\x => k x <*> p) 
  Val f   <*> p = map f p

Monad (Prog es) where
  Op op k >>= f = Op op (assert_total (>>= f) . k)
  Val x   >>= f = f x

weaken : Prog es a -> Prog (e :: es) a
weaken (Op op k) = Op (weaken op) (weaken . k)
weaken (Val x)   = Val x

call : {e : Type -> Type} -> {es : List (Type -> Type)} -> {auto ok : NonEmpty es} -> Member e es 
    => e x -> Prog es x
call op = Op (inj op) Val

run : Prog [] a -> a
run (Val x) = x