module Main
import Effect.State
import Effect.Exception
import Data.SortedMap

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

instance Eq Op where
  Add == Add = True
  Mul == Mul = True
  _ == _ = False

instance Show Op where
  show Add = "+"
  show Mul = "*"

instance Eq il_expr where 
  Stop == Stop = True
  (Var a) == (Var b) = a == b
  (Const a) == (Const b) = a == b
  Unit == Unit = True
  (Pair a b) == (Pair c d) = a == c && b == d
  (Lambda a b) == (Lambda c d) = a == c && b == d
  (Fst a) == (Fst b) = a == b
  (Snd a) == (Snd b) = a == b
  (RunCont a b) == (RunCont c d) = a == c && b == d
  (Arith op1 a b) == (Arith op2 c d) = op1 == op2 && a == c && b == d
  _ == _ = False

instance Show il_expr where
  show (Var v) = v
  show (Const x) = show x
  show Unit = "Unit"
  show (Pair a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
  show (Lambda v e) = "\\" ++ v ++ " . " ++ show e
  show (Fst e) = "fst " ++ show e
  show (Snd e) = "snd " ++ show e
  show (RunCont a b) = "[" ++ show a ++ " <| " ++ show b ++ "]"
  show (Arith op a b) = show a ++ " " ++ show op ++ " " ++ show b
  show Stop = "Stop"

instance Ord il_expr where
  compare a b = compare (show a) (show b)

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
                        
data ILType = IInt | IUnit | IPair ILType ILType | INot ILType | ITypeVar Int | IFalse

instance Show ILType where
  show IInt = "Int"
  show IUnit = "Unit"
  show (IPair t1 t2) = "(" ++ show t1 ++", " ++ show t2 ++ ")"
  show (INot t) = "-" ++ show t
  show (ITypeVar n) = "t" ++ show n
  show IFalse = "0"

Ctx : Type
Ctx = SortedMap il_expr ILType

freshTyVar : { [STATE Int] } Eff m ILType
freshTyVar = do vn <- get
                put (vn + 1)
                pure $ ITypeVar vn

tysub : Int -> ILType -> ILType -> ILType
tysub v sub (ITypeVar n) = if n == v then sub else ITypeVar n
tysub v sub (IPair t1 t2) = IPair (tysub v sub t1) (tysub v sub t2)
tysub v sub (INot t) = INot (tysub v sub t)
tysub v sub t = t

unify : Ctx -> ILType -> ILType -> Either String Ctx
unify ctx (ITypeVar v) t2 = Right $ map (tysub v t2) ctx
unify ctx t1 (ITypeVar v) = Right $ map (tysub v t1) ctx
unify ctx (INot t1) (INot t2) = unify ctx t1 t2
unify ctx (IPair a1 a2) (IPair b1 b2) = unify !(unify ctx a1 b1) a2 b2
unify ctx IInt IInt = Right ctx
unify ctx IUnit IUnit = Right ctx
unify ctx IFalse IFalse = Right ctx
unify ctx t1 t2 = Left $ "cannot unify " ++ show t1 ++ " and " ++ show t2

infer_ilt : Ctx -> il_expr -> { [STATE Int, EXCEPTION String] } Eff m (ILType, Ctx)
infer_ilt ctx expr = 
  case expr of
    Unit => pure (IUnit, ctx)
    Const _ => pure (IInt, ctx)
    Stop => pure (!freshTyVar, ctx)
    Var v => case lookup expr ctx of
               Just t => pure (t, ctx)
               Nothing => do tvar <- freshTyVar
                             let ctx' = insert expr tvar ctx
                             pure (tvar, ctx')
    Lambda v exp => do
      (_, ctx1) <- infer_ilt ctx exp
      (tv, ctx2) <- infer_ilt ctx1 (Var v)
      let ty = INot tv
      let ctx3 = insert expr ty ctx2
      pure (ty, ctx3)
    RunCont e1 e2 => do
      (t2, ctx2) <- infer_ilt ctx e2
      (t1, ctx3) <- infer_ilt ctx2 e1
      case unify ctx3 t1 (INot t2) of
        Left err => raise err
        Right ctx4 => pure (IFalse, ctx4)
    Pair e1 e2 => do
      (t1, ctx1) <- infer_ilt ctx e1
      (t2, ctx2) <- infer_ilt ctx1 e2
      let ty = IPair t1 t2
      let ctx3 = insert expr ty ctx2
      pure (ty, ctx3)
    Fst e => do
      (t, ctx1) <- infer_ilt ctx e
      case t of 
        IPair t1 t2 => pure (t1, ctx1)
        ITypeVar v => do
          t1 <- freshTyVar
          t2 <- freshTyVar
          let ty = IPair t1 t2
          case unify ctx1 t ty of
               Left err => raise err
               Right ctx2 => pure (t1, ctx2)
        _ => raise $ "pair type expected for " ++ show e ++ ", instead found " ++ show t
    Snd e => do
      (t, ctx1) <- infer_ilt ctx e
      case t of 
        IPair t1 t2 => pure (t2, ctx1)
        ITypeVar v => do
          t1 <- freshTyVar
          t2 <- freshTyVar
          let ty = IPair t1 t2
          case unify ctx1 t ty of
               Left err => raise err
               Right ctx2 => pure (t2, ctx2)
        _ => raise $ "pair type expected for " ++ show e ++ ", instead found " ++ show t
    Arith op e1 e2 => do
      (t1, ctx1) <- infer_ilt ctx e1
      (t2, ctx2) <- infer_ilt ctx1 e2
      case unify ctx2 t1 IInt of
        Left err => raise err
        Right ctx3 => case unify ctx3 t2 IInt of
                        Left err => raise err
                        Right ctx4 => pure (IInt, ctx4)
                     


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

typeCheckIL : il_expr -> List String
typeCheckIL e = case the (Either String (ILType, Ctx)) $ run $ infer_ilt empty e of
                  Left err => [err]
                  Right (t, ctx) => map show $ Data.SortedMap.toList ctx


prg2_types : List String
prg2_types = typeCheckIL prg2_il

