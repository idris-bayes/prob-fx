module Wasabaye.Prog

import Data.List.Elem 

Effect = Type -> Type 

data EffectSum : (es : List Effect) -> (a : Type) -> Type where
  Sum : (0 prf : Elem e es) -> (op : e a) -> EffectSum es a

inj : (0 prf : Elem e es) => e a -> EffectSum es a
inj = Sum prf