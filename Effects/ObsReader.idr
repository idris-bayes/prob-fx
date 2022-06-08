module Effects.ObsReader

import Env

data ObsReader : (env : List (String, Type)) -> Type -> Type where 
  -- Ask : 