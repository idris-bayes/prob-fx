module ProbFX.Effects.Writer

import ProbFX.Prog

||| Writing to a stream
public export
data Writer : (w : Type) -> (a : Type) -> Type where
  Tell : Monoid w => (vw : w) -> Writer w ()

public export
tell : (prf : Elem (Writer w) es) => Monoid w => w -> Prog es ()
tell = call . Tell

public export
handleWriter : Monoid w => (prf : Elem (Writer w) es) =>  Prog es a -> Prog (es - Writer w) (a, w)
handleWriter = loop Prelude.neutral
  where
    loop : Semigroup w => w -> Prog es a -> Prog (es - Writer w) (a, w)
    loop w1 (Val x)   = pure (x, w1)
    loop w1 (Op op k) = case discharge op {prf} of
        Left op'        => Op op' (loop w1 . k)
        Right (Tell vw) => loop (vw <+> w1) (k ())
