module Wasabaye.Effects.Writer

import Wasabaye.Prog 

public export
data Writer : (w : Type) -> (a : Type) -> Type where
  Tell : Monoid w => (vw : w) -> Writer w ()

public export
handleWriter : (prf : Elem (Writer w) es) => w -> Prog es a -> Prog (es - Writer w) (a, w)
handleWriter w (Val x)   = pure (x, w)
handleWriter w (Op op k) = case discharge op {prf} of
    Left op'        => Op op' (handleWriter w . k)
    Right (Tell vw) => handleWriter (vw <+> w) (k ())
