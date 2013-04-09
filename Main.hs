{-# OPTIONS_GHC -w #-}
-----------------------------------------------------------------------------
--
-- Module      :  Main
-- Copyright   :
-- License     :  AllRightsReserved
--
-- Maintainer  :
-- Stability   :
-- Portability :
--
-- |
--
-----------------------------------------------------------------------------

module Main where

import Parser

example1 = "(fix fact . \\x . ifzero x 1 (mul x (fact (minus x 1)))) 10"
example2 = "(\\x . mul x (minus x 1)) 10"                                     -- (10*(10-1))                = VI 90
example3 = "(\\x . plus x (plus x 1)) 5"                                      -- (5+(5+1))                  = VI 11
example4 = "(let w = (\\x . ifzero x 5 (minus x 1)) 5 in (\\y . plus y w) 4)" -- (ifz 5 5 (5-1)) into (4+x) = VI 8
example5 = "gcd 125 (gcd 10 25)"                                              -- (GCD (125;GCD(10;25))      = VI 5
example6 = "mul (minus 5 2) (div 125 (div 25 10))"                            -- (5-2)*(125/(25/10))        = VI 186

{- Euclide Algorithm used for Greatest Common Divisor
    function gcd(a, b)
        if a = 0
           return b
        while b /= 0
            if a > b
               a := a âˆ’ b
            else
               b := b âˆ’ a
        return a
-}

-- Definition of an environment with pairs of (Variable, Value) and Value being an integer or a function of integers
data Typ = N | !Typ :> !Typ deriving (Show, Eq)
type TEnv = [(Var, Typ)]

infixl 9 :>

-- Working environment with empty list of (Variable, Type) pairs
tenv0 :: TEnv
tenv0 = [
        ("ifzero", N :> (N :> (N :> N))),
        ("plus", N :> (N :> N)),
        ("minus", N :> (N :> N)),
        ("div", N :> (N :> N)),
        ("mul", N :> (N :> N)),
        ("gcd", N :> (N :> N))
       ]

-- Look up the variable to check if existing in the environment
tlkup :: TEnv -> Var -> Typ
tlkup tenv x = maybe err id $ lookup x tenv
        where err = error $ "Unbound variable " ++ x
        
-- Append (variable, value) in the environment
text :: TEnv -> (Var,Typ) -> TEnv
text tenv xt = xt : tenv

--tsel :: Exp -> Maybe Exp
--tsel tenv exp = 

-- Type Checker
teval :: TEnv -> Exp -> Typ
teval tenv (BuiltIn (Nat n)) = N                                    -- Natural Integer
teval tenv (Fix x t)         = teval (text tenv (x,N :> N)) t       -- fix x.M
teval tenv (Let x t1 t2)     = teval (text tenv (x, teval tenv t1)) t2   -- let ... in ...
teval tenv (Abstract x t)    = (N :> teval (text tenv (x, N)) t)    -- Lambda abstraction
teval tenv (LVar x)          = tlkup tenv x                         -- Variable
teval tenv (t1 :$ t2)        =                                      -- Function application
    let v1 = teval tenv t1
        v2 = teval tenv t2
    in case v1 of
       v1a :> v1r | v1a == v2 -> v1r
       v1a :> v1r -> error $ unwords ["Applying a function of arg type",
                                      show v1a, "to argument of type",
                                      show v2]
       v1 -> error $ "Trying to apply a non-function: " ++ show v1
----------------------------------------------------------------------------------------
data Value = VI Integer
            | VC (Value -> Value)
            | VT (Value -> Value -> Value)

type Env = [(Var, Value)]

env0 :: Env
env0 = [
        ("plus", VT vtplus),
        ("minus", VT vtminus),
        ("mul", VT vtmul),
        ("div", VT vtdiv),
        ("gcd", VT vtgcd)
        ]

vtplus :: Value -> Value -> Value                                    -- primitive function plus
vtplus e1 e2 =
    case (e1,e2) of
        (VI n1, VI n2) -> VI (n1+n2)
        vs -> error $ "Trying to add non-integers: " ++ show vs
vtminus :: Value -> Value -> Value                                   -- primitive function minus
vtminus e1 e2 =
    case (e1,e2) of
        (VI n1, VI n2) -> VI (n1-n2)
        vs -> error $ "Trying to substract non-integers: " ++ show vs
vtmul :: Value -> Value -> Value                                     -- primitive function multiply
vtmul e1 e2 =
    case (e1,e2) of
        (VI n1, VI n2) -> VI (n1*n2)
        vs -> error $ "Trying to multiply non-integers: " ++ show vs
vtdiv :: Value -> Value -> Value                                     -- primitive function divide
vtdiv e1 e2 =
    case (e1,e2) of
        (VI n1, VI n2) -> VI (n1 `div` n2)
        vs -> error $ "Trying to divide non-integers: " ++ show vs
vtgcd :: Value -> Value -> Value                                     -- euclid's algorithm - greatest common divisor
vtgcd e1 e2 =
    case (e1,e2) of
        (VI n1, VI n2) -> if (n1 == 0)
                            then VI n2
                          else VI (gcd2 n1 n2)
        vs -> error $ "Trying to get the greatest common divisor from non-integers: " ++ show vs
gcd2 :: Integer -> Integer -> Integer
gcd2 a b =
    case b of
    0 -> a
    _ -> case (a > b) of
        True  -> gcd2 (a-b) b
        False -> gcd2 a (b-a)

ifzero :: Env -> Exp -> Exp -> Exp -> Value                          -- primitive function ifzero
ifzero env e1 e2 e3 =
    let v1 = eval env e1
    in case v1 of
        VI 0 -> eval env e2
        VI _ -> eval env e3
        v -> error $ "Trying to compare a non-integer to 0: " ++ show v

-- Look up the variable to check if existing
lkup :: Env -> Var -> Value
lkup env x = maybe err id $ lookup x env
  where err = error $ "Unbound variable " ++ x
{-
let y = lookup x tenv
        in case y of
        Nothing -> Undefined
        Just Undefined ->
        Just z -> z-}
-- Append (variable, value) in the environment
ext :: Env -> (Var,Value) -> Env
ext env xt = xt : env

instance Show Value where
    show (VI n) = "VI " ++ show n
    show (VC _) = "<coupled function>"
    show (VT _) = "<tripled function>"

-- Simple Interpreter
eval :: Env -> Exp -> Value
eval env (BuiltIn (Nat n)) = VI n                                     -- Natural Integer
eval env (Fix x t)         = eval env (Abstract x (Fix x t))          -- fix x.M
eval env (Let x e1 e2)     = eval (ext env (x, eval env e1)) e2       -- let ... in ...
eval env (Abstract x e)    = VC (\v -> eval (ext env (x,v)) e)        -- Lambda abstraction
eval env (LVar x)          = lkup env x                               -- Variable
eval env (LVar "ifzero" :$ e1 :$ e2 :$ e3) = ifzero env e1 e2 e3
eval env (e1 :$ e2 :$ e3)  =                                          -- Tripled Function application
    let v1 = eval env e1
        v2 = eval env e2
        v3 = eval env e3
    in case v1 of
        VT f -> f v2 v3
        v -> error $ "Trying to apply a non-tripled-function: " ++ show v
eval env (e1 :$ e2)        =                                          -- Coupled Function application
    let v1 = eval env e1
        v2 = eval env e2
    in case v1 of
        VC f -> f v2
        v -> error $ "Trying to apply a non-coupled-function: " ++ show v

-- Main function
main = do
        str <- getLine
        print str
        let exp = (lambda . lexer) str
        let typ = teval tenv0 exp
        if (typ == N)
            then do print "Typed-checking successful\nInterpretation in process\n"
                    let res = eval env0 exp
                    print res
                else error $ "Typed-checking failed with type: " ++ show typ




