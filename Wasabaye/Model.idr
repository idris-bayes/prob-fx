module Wasabaye.Model

import Wasabaye.Prog
import Wasabaye.Effects.Dist
import Wasabaye.Effects.ObsReader

Model : (env : List (String, Type)) -> (effs : List (Type -> Type)) -> (ret : Type) -> Type
Model env es a = (Member Dist es, Member (ObsReader env) es) => Prog es a