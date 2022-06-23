module Wasabaye.EnvVec

import Data.List
import Data.List.Elem
import Data.Vect

private
data Assign : String -> Nat -> Type -> Type where
  MkAssign : {0 n : Nat} -> (x : String) -> (trace : List a) -> Assign x n a

public export
data Env : List (String, Nat, Type)  -> Type where
  ENil  : Env []
  ECons : Assign x n a -> Env env -> Env ((x, n, a) :: env)

infixr 10 ::=
public export
(::=) : (x : String) -> (trace : Vect n a) -> Assign x n a
(::=) x vs = MkAssign x {n} (toList vs)

infixr 10 <:>
public export
(<:>) : Assign x n a -> Env env -> Env ((x, n, a) :: env)
(<:>) xv env = ECons xv env

public export
Observable : (env : List (String, Nat, Type)) -> (var : String) -> (var_type : Type) -> Type
Observable env x a = Elem (x, a) (map (\(var, m, ty) => (var, ty)) env)

public export
ObservableV : (env : List (String, Nat, Type)) -> (var : String) -> (n : Nat) -> (var_type : Type) -> Type
ObservableV env x n a = Elem (x, n, a) env

public export
get : (x : String) -> Env env -> {auto prf : Elem (x, n, a) env } -> List a
get x (ECons (MkAssign x v) xvs) {prf = Here}   = v
get x (ECons other xvs) {prf = There later}     = get x xvs {prf = later} 

public export
set : (x : String) -> (trace : List a) -> Env env -> {auto prf : Elem (x, n, a) env} -> Env env
set x v (ECons (MkAssign x _) xvs) {prf = Here}   = ECons (MkAssign x v) xvs
set x v (ECons other xvs) {prf = There later}     = ECons other (set x v xvs {prf = later})

public export
update : (x : String) -> (List a -> List a) -> Env env -> {auto prf : Elem (x,n, a) env} -> Env env
update x f (ECons (MkAssign x v) xvs) {prf = Here}   = ECons (MkAssign x (f v)) xvs
update x f (ECons other xvs) {prf = There later}     = ECons other (update x f xvs {prf = later})

exampleEnv : Env [("x", 0, Int), ("y", 0, Int)]
exampleEnv = ("x" ::= []) <:> ("y" ::= []) <:> ENil