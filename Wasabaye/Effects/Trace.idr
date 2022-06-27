module Wasabaye.Effects.Trace

import Data.List
import Wasabaye.Env
import Wasabaye.Prog
import Wasabaye.PrimDist
import Wasabaye.Effects.Dist

||| Primitive values
public export
data PrimVal = PrimDouble Double | PrimNat Nat | PrimBool Bool

public export
Trace : Type
Trace = List (String, List PrimVal)

export
primDistToPrimVal : PrimDist a -> (a -> PrimVal)
primDistToPrimVal (Normal _ _)   = PrimDouble 
primDistToPrimVal (Uniform _ _)  = PrimDouble 
primDistToPrimVal (Bernoulli _)  = PrimBool 
primDistToPrimVal (Binomial _ _) = PrimNat 

export
insertTrace : (String, PrimVal) -> Trace -> Trace
insertTrace (x, val) ((y, vals) :: rest) with (x == y)
    _ | True  = (y, val :: vals) :: rest
    _ | False = (y, vals) :: insertTrace (x, val) rest
insertTrace (x, val) [] = [(x, [val])]

||| Handler for recording samples 
traceSamples' : (prf : Elem Sample es) => Trace -> Prog es a -> Prog es (a, Trace)
traceSamples' strace (Val x) = pure (x, strace) 
traceSamples' strace (Op op k) with (prj op {prf})
  _ | Just (MkSample d maybe_tag) with (maybe_tag)
    _ | Just tag = do y <- send (MkSample d maybe_tag) 
                      let p = primDistToPrimVal d y
                          strace' = insertTrace (tag, p) strace 
                      (traceSamples' strace' . k) y
    _ | Nothing  = do y <- send (MkSample d maybe_tag)
                      (traceSamples' strace . k) y
  _ | Nothing = Op op (traceSamples' strace . k)

public export
traceSamples : (prf : Elem Sample es) => Prog es a -> Prog es (a, Trace)
traceSamples = traceSamples' []

||| Converting sample traces to output environments
fromPrimVal : {ty : Type} -> PrimVal -> Maybe ty 
fromPrimVal {ty=Double} (PrimDouble x) = Just x 
fromPrimVal {ty=Nat}    (PrimNat x)    = Just x
fromPrimVal {ty=Bool}   (PrimBool x)   = Just x
fromPrimVal _                          = Nothing 

fromPrimVals : {x : String} -> {ty : Type} -> List PrimVal -> Assign x ty
fromPrimVals pvs with (sequence $ map (fromPrimVal {ty}) pvs) 
  _ | Just vals = x ::= vals 
  _ | Nothing   = x ::= []

public export
fromTrace : (env : List (String, Type)) -> {auto prf : Env env} -> Trace -> Env env
fromTrace Nil               {prf = ENil}      _ = ENil
fromTrace ((x, ty) :: rest) {prf = ECons _ _} strace with (lookup x strace)
  _ | Just prim_vals = ECons (fromPrimVals {x} {ty} prim_vals) (fromTrace rest strace) 
  _ | Nothing        = ECons (x ::= []) (fromTrace rest strace) 
