module Wasabaye.Examples.LinRegr

import Wasabaye.Model 

linRegr : (prf : Observables env ["y", "m", "c", "std"] Double) =>  List Double -> Model env es (List Double)
linRegr xs = do
  m <- normal {env} 0 3 "m"
  ?t