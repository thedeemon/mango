module Main
import Effect.State

data Op = Add | Mul
var : Type
var = String

name : Type
name = String

data il_expr = Var name | Const Int | Unit | Pair il_expr il_expr | Lambda name il_expr
             | Fst il_expr | Snd il_expr 
             | RunCont il_expr il_expr -- e1 e2
             | Arith Op il_expr il_expr
             | Stop

mutual 
  data rt_val = VInt Int | VUnit | VPair rt_val rt_val | VCont name il_expr Env | VStop

  Env : Type
  Env = List (name, rt_val)

RtVal : Type
RtVal = Either String rt_val 

getv : Env -> name -> RtVal
getv env var with (lookup var env)
  | Just v = Right v
  | Nothing = Left $ "unknown var " ++ var

doArith : Op -> rt_val -> rt_val -> RtVal
doArith Add (VInt a) (VInt b) = Right $ VInt (a + b)
doArith Mul (VInt a) (VInt b) = Right $ VInt (a * b)
doArith _ _ _ = Left "bad args in Arith"


eval_il : Env -> il_expr -> RtVal 
eval_il env (Var v) = getv env v
eval_il env (Const n) = return $ VInt n 
eval_il env Unit = return VUnit
eval_il env (Pair e1 e2) =  [| VPair (eval_il env e1) (eval_il env e2) |]
eval_il env (Fst e) = map (\(VPair a b) => a) $ eval_il env e
eval_il env (Snd e) = map (\(VPair a b) => b) $ eval_il env e 
eval_il env (Lambda v e) = return $ VCont v e env
eval_il env (RunCont ef ex) = Left "trying to eval runcont"
eval_il env (Arith op e1 e2) = doArith op !(eval_il env e1) !(eval_il env e2) 
eval_il env Stop = return VStop

run_il : Env -> il_expr -> RtVal
run_il env (RunCont ef ex) = do
  vf <- eval_il env ef
  vx <- eval_il env ex
  case vf of
    VCont n e env0 => run_il ((n,vx)::env0) e
    VStop => return vx
    _ => Left "bad fun_expr in RunCont"
run_il env e = eval_il env e

subst : name -> il_expr -> il_expr -> il_expr
subst var sub ex = 
  case ex of
    Const _ => ex
    Unit => ex
    Pair e1 e2 => Pair (subst var sub e1) (subst var sub e2)
    Fst e => Fst $ subst var sub e
    Snd e => Snd $ subst var sub e
    Var name => if name == var then sub else ex
    Lambda v e => if var == v then ex else Lambda v (subst var sub e)
    RunCont e1 e2 => RunCont (subst var sub e1) (subst var sub e2)
    Arith op e1 e2 => Arith op (subst var sub e1) (subst var sub e2)
                        

--
t1 : il_expr
t1 = Pair (Const 1) (Const 2)

swp : il_expr
swp = Lambda "p" (Pair (Snd (Var "p")) 
                       (Fst (Var "p")))

data Term = TVar name | TConst Int | TUnit | TLambda name Term | TApply Term Term
             | TPair Term Term | TFst Term | TSnd Term | TArith Op Term Term


mkvar : String -> { [STATE Int] } Eff id String
mkvar v = do n <- get
             put (n+1)
             return $ v ++ show n

mutual
  lz : Term -> { [STATE Int] } Eff id il_expr
  lz e = do
    k <- mkvar "k"
    return $ Lambda k !(compile_lazy (Var k) e)

  compile_lazy : il_expr -> Term -> { [STATE Int] } Eff id il_expr
  compile_lazy k (TVar name) = pure $ RunCont (Var name) k
  compile_lazy k (TConst n) = pure $ RunCont k (Const n)
  compile_lazy k TUnit = pure $ RunCont k Unit
  compile_lazy k (TLambda arg expr) = do
    w <- mkvar "w"
    exp <- compile_lazy (Snd (Var w)) expr 
    return $ RunCont k (Lambda w (subst arg (Fst(Var w)) exp))
  compile_lazy k (TApply e1 e2) = do
    x <- mkvar "x" 
    compile_lazy (Lambda x (RunCont (Var x) (Pair !(lz e2) k))) e1
  compile_lazy k (TPair e1 e2) = pure $ RunCont k (Pair !(lz e1) !(lz e2))
  compile_lazy k (TFst e) = do
    p <- mkvar "p" 
    compile_lazy (Lambda p (RunCont (Fst (Var p)) k)) e
  compile_lazy k (TSnd e) = do
    p <- mkvar "p"
    compile_lazy (Lambda p (RunCont (Snd (Var p)) k)) e
  compile_lazy k (TArith op e1 e2) = do
    v1 <- mkvar "a"
    v2 <- mkvar "b"
    compile_lazy (Lambda v1 
                   !(compile_lazy 
                     (Lambda v2 (RunCont k (Arith op (Var v1) (Var v2)))
                     ) e2)
                 ) e1
    
--
f : Term
f = TLambda "a" (TLambda "b" (TArith Add (TVar "a") (TVar "b")))

v1 : Term
v1 = TConst 5
v2 : Term
v2 = TConst 3

prg : Term
prg = TApply (TApply f v1) v2

prg_il : il_expr
prg_il = runPure $ compile_lazy Stop prg

prg2 : Term
prg2 = TFst (TPair (TConst 2) TUnit)

prg2_il : il_expr
prg2_il = runPure $ compile_lazy Stop prg2

prg3 : Term
prg3 = TArith Add (TConst 1) (TConst 2)

prg3_il : il_expr
prg3_il = runPure $ compile_lazy Stop prg3
