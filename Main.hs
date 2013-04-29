module Main where

import Parser
import qualified Data.IntMap as M

-- Greater Common Divisor
exModulo = "(minus a (mul b (div a b)))";
exGCD = "(fix gcd . \\a . \\b . ifzero b a (gcd b " ++ exModulo ++ "))";
{- Euclide Algorithm used for Greatest Common Divisor
function gcd(a, b)
    while b ≠ 0
       t := b
       b := a mod t
       a := t
    return a		
-}
exGCD1 = exGCD ++ " 25 10";

exFix = "fix x . 1"

example0 = "minus 5 2"
example01 = "ifzero 1 5 2"
example02 = "plus 5 (minus 5 3)"
example1 = "(fix fact . \\x . ifzero x 1 (mul x (fact (minus x 1)))) 10"
example2 = "(\\x . mul x (minus x 1)) 10"                                     -- (10*(10-1))                = VI 90
example3 = "(\\x . plus x (plus x 1)) 5"                                      -- (5+(5+1))                  = VI 11
example4 = "(let w = (\\x . ifzero x 5 (minus x 1)) 5 in (\\y . plus y w) 4)" -- (ifz 5 5 (5-1)) into (4+x) = VI 8
--example5 = "gcd 125 (gcd 10 25)"                                              -- (GCD (125;GCD(10;25))      = VI 5
example5 = "let x = (minus 4 1) in x"
example6 = "mul (minus 5 2) (div 125 (div 25 10))"                            -- (5-2)*(125/(25/10))        = VI 186
example7 = "let x = plus (let y = 5 in plus y 1) 5 in mul x 2" 
example8 = "(\\x . \\y . plus x y) 5 6"
example9 = "(\\x . \\y . \\t . plus x (minus t y)) 5 6 10"
example10 = "(\\x . plus 4 x) ((\\y . minus y 5) 10)"

-- Definition of an environment with pairs of (Variable, Value) and Value being an integer or a function of integers
data Typ = TInt | !Typ :> !Typ | TV TVarName deriving (Show, Eq)
type TVarName = Int
-- variable environment
data TVE = TVE Int (M.IntMap Typ)
type TEnv = [(Var, Typ)]

infixl 9 :>

-- Working Variable Environment with empty context initialized afterwards
tve0 :: TVE
tve0 = TVE 0 M.empty

tenv0 :: TEnv     -- Initialize context of the variable environment
tenv0 = [ ("ifzero", TInt :> (TInt :> (TInt :> TInt))),
		  ("plus", TInt :> (TInt :> TInt)),
		  ("minus", TInt :> (TInt :> TInt)),
		  ("div", TInt :> (TInt :> TInt)),
		  ("mul", TInt :> (TInt :> TInt)) 
	]

tlkup :: TEnv -> Var -> Typ	
tlkup env x = maybe err id $ lookup x env
	where err = error $ "Unbound variable " ++ x
	
text :: TEnv -> (Var,Typ) -> TEnv
text env xt = xt : env

-- Look up the equation to check if existing in the environment
tvlkup :: TVE -> TVarName -> Maybe Typ
tvlkup (TVE _ s) v = M.lookup v s
        
-- Append typed equation in the environment
tvext :: TVE -> (TVarName,Typ) -> TVE
tvext (TVE c s) (tv,t) = TVE c (M.insert tv t s)

-- Insert a new equation
newtv :: TVE -> (Typ,TVE)
newtv (TVE n s) = (TV n, TVE (succ n) s)

-- Chase equations
tvsub :: TVE -> Typ -> Typ
tvsub tve (t1 :> t2) = tvsub tve t1 :> tvsub tve t2
tvsub tve (TV v) | Just t <- tvlkup tve v = tvsub tve t
tvsub tve t = t

-- Unification algorithm
unify :: Typ -> Typ -> TVE -> Either String TVE
unify t1 t2 tve = unify2 (tvchase tve t1) (tvchase tve t2) tve -- chase t1 t2 into unify'

-- shallow chase through a substitution :
-- stop at the last equivalent type variable
tvchase :: TVE -> Typ -> Typ
tvchase tve (TV v) | Just t <- tvlkup tve v = tvchase tve t
tvchase _ t = t

-- If either t1 or t2 are type variables, they must be unbound
unify2 :: Typ -> Typ -> TVE -> Either String TVE
unify2 TInt TInt = Right                 -- two constants unify
unify2 (TV v1) t2 = unifyv v1 t2         -- unify' left variable with right term
unify2 t1 (TV v2) = unifyv v2 t1         -- unify' left term with right variable
unify2 (t1a :> t1r) (t2a :> t2r) = either Left (unify t1r t2r) . unify t1a t2a -- unify' left terms and unify' right terms
unify2 t1 t2 = const (Left $ unwords ["constant mismatch:", show t1, "and", show t2]) -- unknown case

-- Unify a free variable v1 with v2
unifyv :: TVarName -> Typ -> TVE -> Either String TVE
unifyv v1 (TV v2) tve =
	if v1 == v2 
		then Right tve
	else Right (tvext tve (v1, TV v2)) -- record new constraint
unifyv v1 t2 tve = 
	if occurs v1 t2 tve 
		then Left $ unwords ["occurs check:", show (TV v1), "in", show (tvsub tve t2)]   -- case of occur-check ("x=f(x)") 
	else Right (tvext tve (v1,t2))
	
-- The occurs check: if v appears free in t
occurs :: TVarName -> Typ -> TVE -> Bool
occurs v TInt _ = False    -- if v is a constant
occurs v (t1 :> t2) tve = occurs v t1 tve || occurs v t2 tve -- in case of a typed function (t1 :> t2)
occurs v (TV v2) tve =     -- in case of a type variable
	case tvlkup tve v2 of
		Nothing -> v == v2
		Just t -> occurs v t tve

-- Type Checker Helper (does almost all of the type-checker's job
teval2 :: TEnv -> Exp -> (TVE -> (Typ,TVE))         
teval2 env (BuiltIn (Nat n)) = \tve0 -> (TInt,tve0)             -- integer constant
teval2 env (Abstract x e) = \tve0 ->
	let
	(tv,tve1) = newtv tve0
	(te,tve2) = teval2 (text env (x, tv)) e tve1
	in (tv :> te, tve2)
teval2 env (Fix x t) = \tve0 ->                                 -- fix x.M
	let 
	(tv, tve1) = teval2 env (Abstract x t) tve0   -- type-check Lx.t
	(tb, tve2) = newtv tve1
	in case unify tv (tb :> tb) tve2 of
		Right tve -> (tb,tve)
		Left err -> error $ "The fix operator does not unify with the type Int->Int" ++ err ++ "\n"
teval2 env (Let x e1 e2) = \tve0 ->                             -- let
	let
	(t1, tve1) = teval2 env e1 tve0	
	in teval2 (text env (x, t1)) e2 tve1
teval2 env (LVar "ifzero" :$ e1 :$ e2 :$ e3) = \tve0 ->   -- ifzero primitive function
	let
	(t1,tve1) = teval2 env e1 tve0
	(t2,tve2) = teval2 env e2 tve1
	(t3,tve3) = teval2 env e3 tve2
	in case unify t1 TInt tve3 of -- if the first arg unifies with TInt
		Right tve -> case unify t2 t3 tve of -- both last args need unify
			Right tve -> (t2,tve)
			Left err -> error $ unwords ["Branches of ifzero have different types\nUnification failed:", err]
		Left err -> error $ "Trying to compare a non-integer to 0: " ++ err
teval2 env (LVar x :$ e1 :$ e2) = \tve0 ->                      -- primitive functions in initial context
	let 
	v = tlkup env x -- primitive variable
	(t1,tve1) = teval2 env e1 tve0 -- first arg
	(t2,tve2) = teval2 env e2 tve1 -- second arg
    in case either Left (unify t2 TInt) . unify t1 TInt $ tve2 of -- if both args unify with TInt
	    Right tve -> (TInt,tve)	-- if they do, return TInt
	    Left err -> error $ "Trying to operate non-integers: " ++ err
teval2 env (LVar x) = \tve0 -> (tlkup env x, tve0)
teval2 env (e1 :$ e2) = \tve0 ->                            -- lambda application
	let
	(t1,tve1) = teval2 env e1 tve0
	(t2,tve2) = teval2 env  e2 tve1 
	(t1r,tve3)= newtv tve2
	in case unify t1 (t2 :> t1r) tve3 of
		Right tve -> (t1r,tve)
		Left err -> error err

-- Type-Checker (chase type vars as far as possible)
teval :: TEnv -> Exp -> Typ
teval tenv e = 
	let (t,tve) = teval2 tenv e tve0 
		in tvsub tve t
		
----------------------------------------------------------------------------------------
data Value = VI Integer                    -- Integer Value
			| VE Exp                       -- Expression Value
            | VC (Value -> Value)          -- Function from one Value
            | VT (Value -> Value -> Value) -- Function from two Values

type Env = [(Var, Value)]

env0 :: Env
env0 = [
        ("plus", VT vtplus),
        ("minus", VT vtminus),
        ("mul", VT vtmul),
        ("div", VT vtdiv)
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
  where err = error $ "Unbound variable or term " ++ x

-- Append (variable, value) in the environment
ext :: Env -> (Var,Value) -> Env
ext env xt = xt : env

instance Show Value where
    show (VI n) = "VI " ++ show n
    show (VE x) = "<term value>[" ++ show x ++ "]"
    show (VC y) = "<coupled function>"
    show (VT _) = "<tripled function>"

-- Simple Interpreter
eval :: Env -> Exp -> Value
eval env (BuiltIn (Nat n))   = VI n                                     -- Natural Integer
eval env ((Fix x e):$ y :$ z)= eval env (Fix x (e :$ y :$ z)) -- to take in account the fix with two arguments
eval env (Fix x t)           = eval env ((Abstract x t) :$ (Fix x t))   -- fix x.M
eval env ((Abstract x e):$ t)= eval (ext env (x, VE t)) e               -- Beta Reduction (\x.e) t = e[x:=t]
eval env (Let x e1 e2)       = eval (ext env (x, eval env e1)) e2       -- let ... in ...
eval env (Abstract x e)      = VC (\v -> eval (ext env (x,v)) e)        -- Lambda abstraction
eval env (LVar x)            = 										    -- Variable
		let y = lkup env x 
		in case y of
		VE e -> eval env e 
		_ -> y
eval env (LVar "ifzero" :$ e1 :$ e2 :$ e3) = ifzero env e1 e2 e3
eval env (LVar x :$ e1 :$ e2)    =                                    -- Primitive Function application
    let v0 = lkup env x
	in case v0 of
		VT ft -> ft (eval env e1) (eval env e2)
		_ -> v0
		
eval env (e1 :$ e2) =                                                 -- Coupled Function application
    let v1 = eval env e1
        v2 = eval env e2
    in case v1 of
        VC f -> f v2
        VE e -> eval env (e :$ e2)  -- terms from beta reduction interpreted
        v -> error $ "Trying to apply a non-coupled-function: " ++ show v
		
-- Main function
main = do
        str <- getLine
        print str
        let exp = (lambda . lexer) str
        let typ = teval tenv0 exp
        if (typ == TInt)
            then do print "Typed-checking successful\nInterpretation in process\n"
                    let res = eval env0 exp
                    print res
                else error $ "Typed-checking failed with type: " ++ show typ




