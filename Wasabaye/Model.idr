module Wasabaye.Model

import public Wasabaye.Env
import public Wasabaye.PrimDist
import public Wasabaye.Effects.Dist
import public Wasabaye.Effects.ObsReader
import public Wasabaye.Prog

-- | Model as a type-level function, specifying a program with two proofs of membership
public export
Model : (env : List (String, Type)) -> (es : List (Type -> Type)) -> (ret : Type) -> Type 
Model env es a = (Elem Dist es, Elem (ObsReader env) es) => Prog es a 

public export
runModel : (Elem Dist es, Elem (ObsReader env) es) => Model env es a -> Prog es a
runModel m = m

public export
handleCore : Env env -> Model env (Dist :: ObsReader env :: es) a -> Prog (Observe :: Sample :: es) a
handleCore env' = handleDist . handleObsRead env' . runModel

exampleModel : Model env es Int
exampleModel = pure 5

exampleHdlModel : Prog (Observe :: Sample :: []) Int
exampleHdlModel = handleCore ENil (exampleModel {env = []})

-- | Distribution smart constructors
public export
normal : {auto 0 env : _} -> Double -> Double -> (x : String) -> (prf : Observable env x Double) => Model env es Double
normal mu sigma x = do
  maybe_v <- call (Ask {prf} x)
  call (MkDist (Normal mu sigma) maybe_v (Just x))

public export
normal' : Double -> Double -> Model env es Double
normal' mu sigma = do
  call (MkDist (Normal mu sigma) Nothing Nothing)

public export 
uniform : {auto 0 env : _} -> Double -> Double -> (x : String) -> (prf : Observable env x Double) => Model env es Double
uniform min max x = do
  maybe_v <- call (Ask {prf} x)
  call (MkDist (Uniform min max) maybe_v (Just x))

public export
uniform' : Double -> Double -> Model env es Double
uniform' min max = do
  call (MkDist (Uniform min max) Nothing Nothing)

public export
discrete' : List Double -> Model env es Int
discrete' xs = do
  call (Dist (DiscreteDist xs) Nothing Nothing)

-- public export
-- discrete : [Double] -> x -> Observable env x Int
--   -> Model env es Int
-- discrete xs field = Model $ do
--   let tag = Just $ varToStr field
--   maybe_y <- ask @env field
--   call (Dist (DiscreteDist xs) maybe_y tag)

-- categorical : forall env es v x. (Eq v, Show v, OpenSum.Member v PrimVal) => Observable env x v
--   => List (v, Double) -> ObsVar x
--   -> Model env es v
-- categorical xs field = Model $ do
--   let tag = Just $ varToStr field
--   maybe_y <- ask @env field
--   call (Dist (CategoricalDist xs) maybe_y tag)

-- categorical' : (Eq v, Show v, OpenSum.Member v PrimVal) => [(v, Double)] -> Model env es v
-- categorical' xs = Model $ do
--   call (Dist (CategoricalDist xs) Nothing Nothing)
