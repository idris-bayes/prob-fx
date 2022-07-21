module ProbFX.Effects.Trace

import Data.List
import Data.Vect
import ProbFX.Env
import ProbFX.Prog
import ProbFX.PrimDist
import ProbFX.Effects.Dist

||| Primitive values
public export
data PrimVal = PrimDouble Double | PrimNat Nat | PrimBool Bool | Prim

||| Trace of sampled values
public export
Trace : Type
Trace = List (String, List PrimVal)

export
toPrimVal : PrimDist a -> (a -> PrimVal)
toPrimVal (Normal _ _)    = PrimDouble
toPrimVal (Uniform _ _)   = PrimDouble
toPrimVal (Bernoulli _)   = PrimBool
toPrimVal (Binomial _ _)  = PrimNat
toPrimVal (Beta _ _)      = PrimDouble
toPrimVal (Gamma _ _)     = PrimDouble
toPrimVal (Poisson _)     = PrimNat
toPrimVal (Categorical _) = PrimNat . finToNat
toPrimVal (Discrete _)    = ?to_do_toPrimVal_discrete
toPrimVal (Dirichlet _)   = ?to_do_toPrimVal_dirichlet

export
insertTrace : (String, PrimVal) -> Trace -> Trace
insertTrace (x, val) ((y, vals) :: rest) with (x == y)
    _ | True  = (y, val :: vals) :: rest
    _ | False = (y, vals) :: insertTrace (x, val) rest
insertTrace (x, val) [] = [(x, [val])]

||| A run-time conversion of sample traces to output environments
fromPrimVal : {ty : Type} -> PrimVal -> Maybe ty
fromPrimVal {ty=Double} (PrimDouble x) = Just x
fromPrimVal {ty=Nat}    (PrimNat x)    = Just x
fromPrimVal {ty=Bool}   (PrimBool x)   = Just x
fromPrimVal _                          = ?to_do_fromPrimVal

fromPrimVals : {x : String} -> {ty : Type} -> List PrimVal -> Assign x ty
fromPrimVals pvs with (sequence $ map (fromPrimVal {ty}) pvs)
  _ | Just vals = x ::= vals
  _ | Nothing   = x ::= []

export
fromTrace : (env : List (String, Type)) -> {auto prf : Env env} -> Trace -> Env env
fromTrace Nil               {prf = ENil}      _ = ENil
fromTrace ((x, ty) :: rest) {prf = ECons _ _} strace with (lookup x strace)
  _ | Just prim_vals = ECons (fromPrimVals {x} {ty} prim_vals) (fromTrace rest strace)
  _ | Nothing        = ECons (x ::= [])                        (fromTrace rest strace)

||| Handler for recording samples
traceSamples' : (prf : Elem Sample es) => Trace -> Prog es a -> Prog es (a, Trace)
traceSamples' strace (Val x) = pure (x, strace)
traceSamples' strace (Op op k) with (prj op {prf})
  _ | Just (MkSample d tag)
        = do  y <- call (MkSample d tag)
              let p = toPrimVal d y
                  strace' = insertTrace (tag, p) strace
              (traceSamples' strace' . k) y
  _ | Nothing = Op op (traceSamples' strace . k)

public export
traceSamples : (prf : Elem Sample es) => Prog es a -> Prog es (a, Trace)
traceSamples = traceSamples' []
