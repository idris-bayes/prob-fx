module ProbFX2.Examples

import ProbFX2.ModelIx

-- | Example models
-- Example 1
exampleModelIx1 : ModelIx [("x", Double)] Double
exampleModelIx1 = do
  x <- normal 0 2 "x"
  Pure x

exampleModelIx1Impl : ModelIx [("x", Double)] Double
exampleModelIx1Impl = do
  ((>>=) {env1 = [("x", Double)]}) (normal 0 2 "x")  (\x => Pure x)

-- Example 2 
exampleModelIx2 : ModelIx [("b", Bool), ("y_0", Double), ("y_1", Double)] Double
exampleModelIx2 = do
  b <- bernoulli 0.5 "b"
  y <- If b (normal 1 1 "y_0") (normal 0 1 "y_1")
  Pure y

-- Example 3
exampleModelIx3 : ModelIx [("b", Bool)] (b ** ModelIx (if b then [("y_0", Double)] else [("y_1", Double)]) Double)
exampleModelIx3 = do
  b <- bernoulli 0.5 "b"
  let m = iF b (normal 1 1 "y_0") (normal 0 1 "y_1")
  case m of (True ** m1)  => Pure (True ** m1)
            (False ** m2) => Pure (False ** m2)

{- Generating variable names dynamically, or having them occur multiple times via iteration or recursion, is a problem.

-- Example 4: Recursion is a problem.
exampleModelIx4 : ModelIx [("y", Double)] Double
exampleModelIx4 = do
  let loop : Nat -> ModelIx [("y", Double)] Double
      loop 0     = normal 0 1 "y"
      loop (S k) = do normal 0 1 "y"
                      loop k
  loop 5

-- Example 5: Iteration is a problem, seeing as how we do not have a proper monad yet. 
exampleModelIx5 : List String -> ModelIx [("y", Double)] Double
exampleModelIx5 xs = do
  let mapModel : List (ModelIx [(s, Double)] Double)
      mapModel = map (\s => normal 0 1 s) xs
  ?ho
-}

-- | Examples: Test evaluating a concrete ModelIx example under an environment instance.
-- Example 2
test_evalModelIx2 : Double
test_evalModelIx2 = evalModelIx exampleModelIx2 (ECons "b" (Just True) (ECons "y_0" (Just 1.0) (ECons "y_1" Nothing ENil)))

-- Example 3
test_evalModelIx3 : Double
test_evalModelIx3 = 
  let branchedModel : (b ** ModelIx (if b then [("y_0", Double)] else [("y_1", Double)]) Double) 
        = evalModelIx exampleModelIx3 (ECons "b" (Just True) ENil)
  in  case branchedModel of (True  ** m1) => evalModelIx m1 (ECons "y_0" (Just 1.0) ENil)
                            (False ** m2) => evalModelIx m2 (ECons "y_1" Nothing ENil)


-- | Examples: Test translating a concrete ModelIx example to a Sample and Observe probabilistic program.
-- Example 2
test_translateModelIx2 : ProbProg  [("b", Bool), ("y_0", Double), ("y_1", Double)] Double
test_translateModelIx2 = translateModelIx exampleModelIx2 (ECons "b" (Just True) (ECons "y_0" (Just 1.0) (ECons "y_1" Nothing ENil)))

-- Example 3
test_translateModelIx3 : ProbProg [("b", Bool)] (b ** ProbProg (if b then [("y_0", Double)] else [("y_1", Double)]) Double)
test_translateModelIx3 = do
  let branchedModel = translateModelIx exampleModelIx3 (ECons "b" (Just True) ENil)
  branchedModel >>= (\case
                      (True ** m1) =>  let probProg1 : ProbProg [("y_0", Double)] Double 
                                                            = translateModelIx m1 (ECons "y_0" (Just 1.0) ENil) 
                                        in  Pure (True ** probProg1)
                      (False ** m2) => let probProg2 : ProbProg [("y_1", Double)] Double 
                                                            = translateModelIx m2 (ECons "y_1" (Just 1.0) ENil) 
                                        in  Pure (False ** probProg2))

-- ||| To think about:
-- 2. How to implement environments that assign traces of values to single variable names. 
--      - Is it possible to read the first value from a variable's trace, put the trace back in the environment, and read the next value from the trace the next time we encounter the variable again? 
--      - Maybe trying to use lists defeats the purpose of this research; perhaps we're translating ideas from Haskell wasabaye too hard, whereas we want to see how expressively we can capture the sample space; perhaps we can't really take advantage of dependent types in the list-approach. Assuming we stick to assigning single values to observable variables, each call to a primitive distribution should have a unique variable name. When we want to have a RV represent multiple values, we could instead provide a multivariate primitive distribution.
-- 3. If the order of values in the environment/trace is determined by the type of the model, are their corresponding variable names essentially redundant (assuming we don't take a list approach)?
-- 4. How to implement distributions that _don't_ take a variable name. Can we take advantage of Idris's variable number of arguments functionality.