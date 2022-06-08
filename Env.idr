module Env

import Data.List.Elem

data Env : List (String, Type) -> Type where
  ENil  : Env []
  ECons : List a -> Env env -> Env ((x, a) :: env)

get : {auto p : Elem (x, a) env} -> (x : String) -> Env env -> a
-- get x 