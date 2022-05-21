module Fusion.Algebra

-- | Transform a state-annotated computation in 'n' to a compution in 'm' whose value is annotated with the final state.
Handler : (ctx : Type -> Type) -> (n : Type -> Type) -> (m : Type -> Type) -> Type
Handler ctx n m = {x : Type} 
               -> ctx (n x) -- A computation in 'n' wrapped in a context functor 'ctx' that associates it to a state.
               -> m (ctx x) -- A computation in 'm' annotated with a state.

-- | All carrier types 'm' must have an Algebra instance specifying how they interpret a specific effect signature 'sig'
interface Monad m => Algebra (sig : (Type -> Type) -> Type -> Type) 
                             (m   : Type -> Type) 
                   | m  where
  alg : Functor ctx
    =>  Handler ctx n m
    ->  sig n a
    ->  ctx ()
    ->  m (ctx a)