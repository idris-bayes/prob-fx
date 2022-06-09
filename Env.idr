module Env

import Data.List
import Data.List.Elem

data Assign : String -> Type -> Type where
  MkAssign : (x : String) -> (trace : List a) -> Assign x a

infixr 10 ::=
(::=) : (x : String) -> (trace : List a) -> Assign x a
(::=) x vs = MkAssign x vs

data Env : List (String, Type)  -> Type where
  ENil  : Env []
  ECons : Assign x a -> Env env -> Env ((x, a) :: env)
 
infixr 10 <:>
(<:>) : Assign x a -> Env env -> Env ((x, a) :: env)
(<:>) xv env = ECons xv env

get : (x : String) -> Env env -> {auto prf : Elem (x, a) env} -> Maybe a
get x (ECons (MkAssign x v) xvs) {prf = Here}   = head' v
get x (ECons other xvs) {prf = There later}     = get x xvs {prf = later} 

set : (x : String) -> (trace : List a) -> Env env -> {auto prf : Elem (x, a) env} -> Env env
set x v (ECons (MkAssign x _) xvs) {prf = Here}   = ECons (x ::= v) xvs
set x v (ECons other xvs) {prf = There later}     = ECons other (set x v xvs {prf = later})

exampleEnv : Env [("x", Int), ("y", Int)]
exampleEnv = ("x" ::= []) <:> ("y" ::= []) <:> ENil

Observable : List (String, Type) -> String -> Type -> Type
Observable env x a  = Elem (x, a) env