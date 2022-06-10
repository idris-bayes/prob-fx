module Wasabaye.Model

import Wasabaye.Env
import Wasabaye.Prog
import Wasabaye.Effects.Dist
import Wasabaye.Effects.ObsReader

-- -- Model as a type-level function, specifying a program with two proofs of membership

Model : (env : List (String, Type)) -> (es : List (Type -> Type)) -> (ret : Type) -> Type 
Model env es a = (Member Dist es, Member (ObsReader env) es) => Prog es a 

runModel : (Member Dist es, Member (ObsReader env) es) => Model env es a -> Prog es a
runModel m = m

handleCore : {env : _} -> {auto es : _} 
  -> Env env -> Model env (ObsReader env :: Dist :: es) a -> Prog (Observe :: Sample :: es) a
handleCore env = handleDist . handleObsRead env . runModel

exampleModel : {auto env : _ } -> Model env es Int
exampleModel = Val 5

exampleHdlModel : Prog (Observe :: Sample :: []) Int
exampleHdlModel = handleCore ENil exampleModel

----------------------
--- Smart constructors 


normal' : {es : _} -> Double -> Double -> Model env es Double
normal' mu sigma = do
  call (MkDist (Normal mu sigma) Nothing)




{- -- -- Model as a data type, whose constructor prepends an abstract type `es` to a program with a concrete effect signature 

data Model1 : (env : List (String, Type)) -> (0 es : List (Type -> Type)) -> (ret : Type) -> Type where
  MkModel1 : Prog (es ++ ObsReader env :: Dist :: Nil) a -> Model1 env es a

runModel1 : Model1 env es a -> Prog (es ++ ObsReader env :: Dist :: Nil) a
runModel1 (MkModel1 prog) = prog

handleCore1 : Env env -> Model1 env [] a -> Prog (Observe :: Sample :: []) a
handleCore1 env = handleDist . handleObsRead env . runModel1

exampleModel1 : Model1 env es Int
exampleModel1 = MkModel1 $ Val 5

exampleHdlModel1 : Prog (Observe :: Sample :: []) Int
exampleHdlModel1 = handleCore1 ENil exampleModel1

-}

{- -- -- Model as a data type, whose constructor stores a Membership

data Model2 : (env : List (String, Type)) -> (0 es : List (Type -> Type)) -> (ret : Type) -> Type where
  MkModel2 : (Member Dist es, Member (ObsReader env) es) => Prog es a -> Model2 env es a

runModel2 : Model2 env (ObsReader env :: Dist :: Nil) a -> Prog (ObsReader env :: Dist :: Nil) a
runModel2 (MkModel2 prog) = prog

handleCore2 : Env env -> Model2 env (ObsReader env :: Dist :: Nil) a -> Prog (Observe :: Sample :: []) a
handleCore2 env = handleDist . handleObsRead env . runModel2

%hint
esHasDist : {es :_} -> Member Dist es
esHasDist = MkMember inj prj

%hint
esHasObsReader : {auto env, es : _} -> Member (ObsReader env) es
esHasObsReader = MkMember inj prj

exampleModel2 : {auto es, env : _} -> Model2 env es Int
exampleModel2 = MkModel2 $ Val 5

-}