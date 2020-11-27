module Interpreter where
import Control.Exception
import Debug.Trace
import Data.List

--
-- Problem 1
-- interpret(x) = x
-- interpret(\x.E1) = \x. interpret(E1)
-- interpret(E1 E2) = let f = interpret(E1)
--                        a = interpret(E2)
--                    in case f of
--                          \x.E3 --> interpret(E3[a/x])
--                              - --> f a
--

---- Data types ----
type Name = String

data Expr =
  Var Name
  | Lambda Name Expr
  | App Expr Expr deriving (Eq,Show)

---- Functions ----
-- Contract: freeVars: Expr -> [all free variables]
-- Purpose: to compute a list of free variables
-- in a given lambda expression
-- Example: freeVars (App (Var "x") (Var "x")) yields ["x"]
-- Definition:
freeVars::Expr -> [Name]
freeVars(Var x) = [x]
freeVars(Lambda n e) = filter(/=n)(freeVars e)
freeVars(App e1 e2) = (union (freeVars e1) (freeVars e2))

-- Contract: freshHelper: [Expr] -> [free variables]
-- Purpose: to recursively compute an infinite list of fresh variables
-- in a given lambda expression
-- Example: freshHelper(App (Var "x") (Var "x")) yields ["x"]
-- Definition:
freshHelper::[Expr] -> [Name]
freshHelper [] = []
freshHelper x = (union (freeVars(head x)) (freshHelper(tail x)))

-- Contract: freshVars: [Expr] -> [available variables]
-- Purpose: takes an expression and returns an infinite list
-- of all non-free variables in the passed expr
-- Example: freshVars [Lambda "1_" (App (Var "x") (App (Var "1_") (Var "2_")))]
-- yields [ "1_","3_","4_","5_","6_","7_","8_", ... ]
-- Definition:
freshVars::[Expr] -> [Name]
freshVars expr_li = ((map (++ "_") (map show [1..10])) \\ freshHelper(expr_li))

-- Contract: subst: (Name, Exprt) -> Expr -> Substituted Expression
-- Purpose: The above function takes a Namee x and an expression
-- m, and returns a function that takes an expression E and returns E
-- with all instances of x replaced by expression m
-- Example: subst ("x", Lambda "x" (Var "x")) (Lambda "y" (Lambda "z" (App (App (Var "x") (Var "y")) (App (Var "x") (Var "z")))))
-- yields Lambda "1_" (Lambda "3_" (App (App (Lambda "x" (Var "x")) (Var "1_")) (App (Lambda "x" (Var "x")) (Var "3_"))))
-- Definition:
subst::(Name, Expr) -> Expr -> Expr
subst(x, m) (Var y)
    | x == y    = m
    | otherwise = (Var y)
subst(x, m) (Lambda y e)
    | x == y              = Lambda y e
    | otherwise           = Lambda (head(freshVars(e:m:(Var x):[]))) (subst(x, m) (subst(y, (Var(head(freshVars(e:m:(Var x):[]))))) e))
subst(x, m) (App e1 e2)   = App(subst(x,m) e1) (subst(x,m) e2)


-- Contract: appNF_OneStep: Expr -> Maybe Expr (Nothing or Just val)
-- Purpose: performs an innermost leftmost reduction one step at a time
-- (applicative order)
-- Example: appNF_OneStep(Lambda "y" (Lambda "x" (Var "x")))
-- yields Nothing
-- Definition:
appNF_OneStep::Expr -> Maybe Expr
-- 1. Variable x -> No reduction needed, just return nothing
appNF_OneStep (Var x) = Nothing
-- 2. Lambda x -> Reduce on the expression e, as we are looking for normal form
appNF_OneStep (Lambda y e) =
  let f = appNF_OneStep(e)
      in case f of
        Nothing -> Nothing
        Just(f') -> Just (Lambda y f')
-- 3. Application with lambda -> Here, we first check to see if the first lambda expression can be replaced
appNF_OneStep(App (Lambda x e1) e2) =
  let f = appNF_OneStep((Lambda x e1)) in case f of
      Nothing -> let a = appNF_OneStep(e2) in case a of
                    Nothing -> Just (subst(x, e2) e1)
                    Just (a') -> Just (App (Lambda x e1) a')
      Just(f') -> Just  (App f' e2)
-- 4. Application without lambda, now we need to check to see if both expressions can be reduced
appNF_OneStep (App e1 e2) =
  let f = appNF_OneStep(e1)
      in case f of
        Nothing -> let a = appNF_OneStep(e2)
                      in case a of
                        Nothing -> Nothing
                        Just(a') -> Just (App e1 a')
        Just(f') ->  Just (App f' e2)

-- Contract: appNF_n: Int -> Expr -> reduced Expr
-- Purpose: Runs the OneStep n times (or until reduced full y),
-- and returns the most reduced version of the passed expression
-- Example: appNF_n 5 (App (App (App (Lambda "x" (Lambda "y" (Lambda "z" (App (App (Var "x") (Var "y")) (App (Var "x") (Var "z")))))) (Lambda "x" (Var "x"))) (Lambda "x" (Var "x"))) (Lambda "x" (Var "x")))
-- yields: App (Lambda "2_" (Var "2_")) (Lambda "x" (Var "x")
-- Definition:
appNF_n :: Int -> Expr -> Expr
appNF_n num ex = if num > 0
  then let f = appNF_OneStep ex in case f of
        (Just othr) -> appNF_n (num-1) othr
        Nothing -> ex
  else ex

  appNF_n :: Int -> Expr -> Expr
  appNF_n n e case n of
    0 -> e
    _ -> case appNF_OneStep(e) of
      Nothing -> e
      (Just e') -> appNF_n (n-1) e
