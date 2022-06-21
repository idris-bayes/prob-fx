module Wasabaye2.Env

import Data.List
import Data.List.Elem

infixr 10 ::=

public export
data Assign : String -> Type -> Type where
  (::=) : (x : String) -> (trace : List a) -> Assign x a

public export
data Env : List (String, Type)  -> Type where
  ENil  : Env []
  ECons : Assign x a -> Env env -> Env ((x, a) :: env)

infixr 10 <:>
public export
(<:>) : Assign x a -> Env env -> Env ((x, a) :: env)
(<:>) xv env = ECons xv env

public export
get : (x : String) -> Env env -> {auto prf : Elem (x, a) env} -> List a
get x (ECons (x ::= v) xvs) {prf = Here}   = v
get x (ECons other xvs) {prf = There later}     = get x xvs {prf = later} 

public export
set : (x : String) -> (trace : List a) -> Env env -> {auto prf : Elem (x, a) env} -> Env env
set x v (ECons (x ::= _) xvs) {prf = Here}   = ECons (x ::= v) xvs
set x v (ECons other xvs) {prf = There later}     = ECons other (set x v xvs {prf = later})

public export
update : (x : String) -> (List a -> List a) -> Env env -> {auto prf : Elem (x, a) env} -> Env env
update x f (ECons (x ::= v) xvs) {prf = Here}   = ECons (x ::= f v) xvs
update x f (ECons other xvs) {prf = There later}     = ECons other (update x f xvs {prf = later})

exampleEnv : Env [("x", Int), ("y", Int)]
exampleEnv = ("x" ::= []) <:> ("y" ::= []) <:> ENil