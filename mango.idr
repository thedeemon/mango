module Main
import Effect.State
import Effect.Exception
import Data.SortedMap

data Op = Add | Mul | Eql | Less
var : Type
var = String

name : Type
name = String

data il_expr = Var name | Const Int | Unit | Stop
             | Lambda name il_expr | RunCont il_expr il_expr -- e1 e2
             | RecLambda name name il_expr -- rec f x e
             | Pair il_expr il_expr | Fst il_expr | Snd il_expr              
             | Arith Op il_expr il_expr            
             | Lefta il_expr | Righta il_expr | Case il_expr il_expr il_expr

instance Eq Op where
  Add == Add = True
  Mul == Mul = True
  Eql == Eql = True
  Less == Less = True
  _ == _ = False

instance Show Op where
  show Add = "+"
  show Mul = "*"
  show Eql = "="
  show Less = "<"

instance Eq il_expr where 
  Stop == Stop = True
  (Var a) == (Var b) = a == b
  (Const a) == (Const b) = a == b
  Unit == Unit = True
  (Pair a b) == (Pair c d) = a == c && b == d
  (Lambda a b) == (Lambda c d) = a == c && b == d
  (RecLambda f a b) == (RecLambda g c d) = a == c && b == d && f == g
  (Fst a) == (Fst b) = a == b
  (Snd a) == (Snd b) = a == b
  (RunCont a b) == (RunCont c d) = a == c && b == d
  (Arith op1 a b) == (Arith op2 c d) = op1 == op2 && a == c && b == d
  (Lefta a) == (Lefta b) = a == b
  (Righta a) == (Righta b) = a == b
  (Case a1 b1 c1) == (Case a2 b2 c2) = a1 == a2 && b1 == b2 && c1 == c2
  _ == _ = False

instance Show il_expr where
  show (Var v) = v
  show (Const x) = show x
  show Unit = "Unit"
  show (Pair a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
  show (Lambda v e) = "\\" ++ v ++ " . " ++ show e
  show (RecLambda f v e) = "\\" ++ f ++ "(" ++ v ++ ") . " ++ show e
  show (Fst e) = "fst " ++ show e
  show (Snd e) = "snd " ++ show e
  show (RunCont a b) = "[" ++ show a ++ " <| " ++ show b ++ "]"
  show (Arith op a b) = show a ++ " " ++ show op ++ " " ++ show b
  show Stop = "Stop"
  show (Lefta e) = "Left " ++ show e
  show (Righta e) = "Right " ++ show e
  show (Case a b c) = "case " ++ show a ++ " { Left -> " ++ show b ++ " | Right -> " ++ show c ++ " }"

instance Ord il_expr where
  compare a b = compare (show a) (show b)

mutual 
  data rt_val = VInt Int | VUnit | VPair rt_val rt_val | VCont name il_expr Env | VStop
              | VLeft rt_val | VRight rt_val 

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
doArith Eql (VInt a) (VInt b) = Right $ if a == b then VRight VUnit else VLeft VUnit
doArith Less (VInt a) (VInt b) = Right $ if a < b then VRight VUnit else VLeft VUnit
doArith _ _ _ = Left "bad args in Arith"

eval_il : Env -> il_expr -> RtVal 
eval_il env (Var v) = getv env v
eval_il env (Const n) = return $ VInt n 
eval_il env Unit = return VUnit
eval_il env (Pair e1 e2) =  [| VPair (eval_il env e1) (eval_il env e2) |]
eval_il env (Fst e) = map (\(VPair a b) => a) $ eval_il env e
eval_il env (Snd e) = map (\(VPair a b) => b) $ eval_il env e 
eval_il env (Lambda v e) = return $ VCont v e env
eval_il env (RecLambda f v e) = return k where k = VCont v e ((f,k)::env)
eval_il env (RunCont ef ex) = Left "trying to eval runcont"
eval_il env (Arith op e1 e2) = doArith op !(eval_il env e1) !(eval_il env e2) 
eval_il env Stop = return VStop
eval_il env (Lefta e) = pure $ VLeft !(eval_il env e)
eval_il env (Righta e) = pure $ VRight !(eval_il env e)
eval_il env (Case e (Lambda x1 e1) (Lambda x2 e2)) =
  case !(eval_il env e) of
    VLeft v  => eval_il ((x1, v)::env) e1
    VRight v => eval_il ((x2, v)::env) e2
    _ => Left "Not a sum type value in Case"
eval_il env (Case _ _ _) = Left "Err: Case with not Lambdas"    

run_il : Env -> il_expr -> RtVal
run_il env (RunCont ef ex) = do
  vf <- eval_il env ef
  vx <- eval_il env ex
  case vf of
    VCont n e env0 => run_il ((n,vx)::env0) e
    VStop => return vx
    _ => Left "bad fun_expr in RunCont"
run_il env (Case e (Lambda x1 e1) (Lambda x2 e2)) =
  case !(eval_il env e) of
    VLeft v  => run_il ((x1, v)::env) e1
    VRight v => run_il ((x2, v)::env) e2
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
    RecLambda f v e => if var == v then ex else RecLambda f v (subst var sub e)
    RunCont e1 e2 => RunCont (subst var sub e1) (subst var sub e2)
    Arith op e1 e2 => Arith op (subst var sub e1) (subst var sub e2)
    Lefta e => Lefta $ subst var sub e
    Righta e => Righta $ subst var sub e
    Case a b c => Case (subst var sub a) (subst var sub b) (subst var sub c)

                        
data ILType = IInt | IUnit | IPair ILType ILType | INot ILType | ITypeVar Int | IFalse | ISum ILType ILType

instance Show ILType where
  show IInt = "Int"
  show IUnit = "Unit"
  show (IPair t1 t2) = "(" ++ show t1 ++", " ++ show t2 ++ ")"
  show (INot t) = "-" ++ show t
  show (ITypeVar n) = "t" ++ show n
  show IFalse = "0"
  show (ISum t1 t2) = "{" ++ show t1 ++ " | " ++ show t2 ++ "}"

Ctx : Type
Ctx = SortedMap il_expr ILType

freshTyVar : { [STATE Int] } Eff ILType
freshTyVar = do vn <- get
                put (vn + 1)
                pure $ ITypeVar vn

tysub : Int -> ILType -> ILType -> ILType
tysub v sub (ITypeVar n) = if n == v then sub else ITypeVar n
tysub v sub (IPair t1 t2) = IPair (tysub v sub t1) (tysub v sub t2)
tysub v sub (INot t) = INot (tysub v sub t)
tysub v sub (ISum t1 t2) = ISum (tysub v sub t1) (tysub v sub t2)
tysub v sub t = t

unify : Ctx -> ILType -> ILType -> Either String Ctx
unify ctx (ITypeVar v) t2 = Right $ map (tysub v t2) ctx
unify ctx t1 (ITypeVar v) = Right $ map (tysub v t1) ctx
unify ctx (INot t1) (INot t2) = unify ctx t1 t2
unify ctx (IPair a1 a2) (IPair b1 b2) = unify !(unify ctx a1 b1) a2 b2
unify ctx IInt IInt = Right ctx
unify ctx IUnit IUnit = Right ctx
unify ctx IFalse IFalse = Right ctx
unify ctx (ISum a1 a2) (ISum b1 b2) = unify !(unify ctx a1 b1) a2 b2
unify ctx t1 t2 = Left $ "cannot unify " ++ show t1 ++ " and " ++ show t2

total
opResTy : Op -> ILType
opResTy Add = IInt
opResTy Mul = IInt
opResTy Eql = ISum IUnit IUnit
opResTy Less = ISum IUnit IUnit

infer_ilt : Ctx -> il_expr -> { [STATE Int, EXCEPTION String] } Eff (ILType, Ctx)
infer_ilt ctx expr = 
  case expr of
    Unit => pure (IUnit, ctx)
    Const _ => pure (IInt, ctx)
    Stop => do ty <- freshTyVar
               pure (ty, insert Stop ty ctx)
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
    RecLambda f v exp => do
      -- exp may have Var f
      (_, ctx1) <- infer_ilt ctx exp
      (tv, ctx2) <- infer_ilt ctx1 (Var v)
      (tf, ctx3) <- infer_ilt ctx2 (Var f)
      let ty = INot tv
      case unify ctx3 ty tf of
        Left err => raise err
        Right ctx4 => pure (ty, insert expr ty ctx4)
    Pair e1 e2 => do
      (t1, ctx1) <- infer_ilt ctx e1
      (t2, ctx2) <- infer_ilt ctx1 e2
      let ty = IPair t1 t2
      let ctx3 = insert expr ty ctx2
      pure (ty, ctx3)
    Fst e => do
      (t, ctx1) <- infer_ilt ctx e
      case t of 
        IPair t1 t2 => pure (t1, insert expr t1 ctx1)
        ITypeVar v => do
          t1 <- freshTyVar
          t2 <- freshTyVar
          let ty = IPair t1 t2
          case unify ctx1 t ty of
               Left err => raise err
               Right ctx2 => pure (t1, insert expr t1 ctx2)
        _ => raise $ "pair type expected for " ++ show e ++ ", instead found " ++ show t
    Snd e => do
      (t, ctx1) <- infer_ilt ctx e
      case t of 
        IPair t1 t2 => pure (t2, insert expr t2 ctx1)
        ITypeVar v => do
          t1 <- freshTyVar
          t2 <- freshTyVar
          let ty = IPair t1 t2
          case unify ctx1 t ty of
               Left err => raise err
               Right ctx2 => pure (t2, insert expr t2 ctx2)
        _ => raise $ "pair type expected for " ++ show e ++ ", instead found " ++ show t
    Arith op e1 e2 => do
      (t1, ctx1) <- infer_ilt ctx e1
      (t2, ctx2) <- infer_ilt ctx1 e2
      case (do unify !(unify ctx2 t1 IInt) t2 IInt) of 
        Left err => raise err
        Right ctx4 => pure (opResTy op, ctx4)
    Lefta e => do
      (t, ctx1) <- infer_ilt ctx e
      t2 <- freshTyVar
      let ty = ISum t t2
      pure (ty, insert expr ty ctx1)
    Righta e => do
      (t, ctx1) <- infer_ilt ctx e
      t1 <- freshTyVar
      let ty = ISum t1 t
      pure (ty, insert expr ty ctx1)
    Case e e1 e2 => do
      (t0, ctx0) <- infer_ilt ctx e
      (t1, ctx1) <- infer_ilt ctx0 e1
      (t2, ctx2) <- infer_ilt ctx1 e2
      case (t1, t2) of
        (INot ty1, INot ty2) =>  
          case unify ctx2 t0 (ISum ty1 ty2) of
            Left err => raise err
            Right ctx3 => pure (IFalse, ctx3)
        _ => raise "Not lambda types found in case"

                     
showCtx : Ctx -> String
showCtx ctx = show $ Data.SortedMap.toList ctx

total
tySharp : ILType -> String
tySharp IInt = "int"
tySharp IUnit = "Unit"
tySharp (IPair a b) = "Pair<" ++ tySharp a ++ ", " ++ tySharp b ++ ">"
tySharp (INot t) = "Kont<" ++ tySharp t ++ ">"
tySharp IFalse = " Err: 0 type "
tySharp (ITypeVar n) = " Err: unresolved type var t" ++ show n
tySharp (ISum a b) = "Sum<" ++ tySharp a ++ ", " ++ tySharp b ++ ">"

addDef : ILType -> String -> {[STATE (List String)]} Eff String
addDef ty s = do xs <- get
                 let f = "f" ++ show (length xs) 
                 put $ (tySharp ty ++ " " ++ f ++ " = " ++ s ++ ";") :: xs
                 return f

Ctx2 : Type
Ctx2 = List (il_expr, ILType)

argTy : ILType -> String
argTy (INot t) = tySharp t
argTy t = "Err: argTy for positive type " ++ show t

--total
genSharp : Ctx2 -> il_expr -> { [STATE (List String), EXCEPTION String] } Eff String
genSharp ctx Unit = pure "unit"
genSharp ctx (Const n) = pure $ show n
genSharp ctx (Var v) = pure v
genSharp ctx (Pair e1 e2) = 
  case lookup (Pair e1 e2) ctx of
    Just (IPair t1 t2) => pure $ "pair<" ++ tySharp t1 ++ ", " ++ tySharp t2 ++">(" ++ 
                                    !(genSharp ctx e1) ++ ", " ++ !(genSharp ctx e2) ++ ")"
    _ => raise $ "Err: no type for " ++ show (Pair e1 e2)
genSharp ctx (Fst e) = pure $ !(genSharp ctx e) ++ ".fst"
genSharp ctx (Snd e) = pure $ !(genSharp ctx e) ++ ".snd"
genSharp ctx (Arith op e1 e2) =
  case op of
    Eql  => pure $  "eql("++ !(genSharp ctx e1) ++", "++ !(genSharp ctx e2) ++")"
    Less => pure $ "less("++ !(genSharp ctx e1) ++", "++ !(genSharp ctx e2) ++")"
    _    => pure $ "("++ !(genSharp ctx e1) ++" "++ show op ++" "++ !(genSharp ctx e2) ++")"
genSharp ctx Stop = case lookup Stop ctx of
                      Nothing => raise "Err: Stop type not found"
                      Just ty => pure $ "x => { throw new Res<" ++ argTy ty ++ ">(x); }"
genSharp ctx (Lambda v e) = let exp = Lambda v e in
                            case lookup exp ctx of
                              Nothing =>  raise $ "Err: unknown type for " ++ show exp ++ " ::: " ++ show ctx
                              Just ty => pure $ v ++ " => " ++ !(genSharp ctx e)
genSharp ctx (RunCont f x) = 
  case lookup f ctx of
    Just (INot t) => pure $ "() => run<" ++ tySharp t ++">("++ !(genSharp ctx f) ++", "++ !(genSharp ctx x) ++")"
    Just t => raise $ "Err?: " ++ show f ++ " has type " ++ show t
    _ => raise $ "Type err with " ++ show f
genSharp ctx (Lefta e) = 
  case lookup (Lefta e) ctx of
    Just (ISum t1 t2) => pure $ "left<" ++ tySharp t1 ++","++ tySharp t2 ++ ">(" ++ !(genSharp ctx e) ++ ")"
    _ => raise $ "Err: no sum type for " ++ show e
genSharp ctx (Righta e) = 
  case lookup (Righta e) ctx of
    Just (ISum t1 t2) => pure $ "right<" ++ tySharp t1 ++","++ tySharp t2 ++ ">(" ++ !(genSharp ctx e) ++ ")"
    _ => raise $ "Err: no sum type for " ++ show e
genSharp ctx (Case e e1 e2) =  
  case lookup e ctx of 
    Just (ISum t1 t2) => pure $ "match<" ++ tySharp t1 ++","++ tySharp t2 ++ ">("  ++ !(genSharp ctx e) ++", "
                               ++ !(genSharp ctx e1) ++", "++ !(genSharp ctx e2) ++ ")"
    _ => raise $ "Err: no sum type for " ++ show e

data Term = TVar name | TConst Int | TUnit | TLambda name Term | TApply Term Term
             | TPair Term Term | TFst Term | TSnd Term | TArith Op Term Term
             | TLeft Term | TRight Term | TCase Term Term Term
             | TIf Term Term Term

infixr 7 =@
(=@) : Term -> Term -> Term
a =@ b = TArith Eql a b

infixr 7 <@
(<@) : Term -> Term -> Term
a <@ b = TArith Less a b

mkvar : String -> { [STATE Int] } Eff String
mkvar v = do n <- get
             put (n+1)
             return $ v ++ show n

mutual
  lz : Term -> { [STATE Int] } Eff il_expr
  lz e = do
    k <- mkvar "k"
    return $ Lambda k !(compile_lazy (Var k) e)

  compile_lazy : il_expr -> Term -> { [STATE Int] } Eff il_expr
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
  compile_lazy k (TLeft e) = pure $ RunCont k (Lefta !(lz e))
  compile_lazy k (TRight e) = pure $ RunCont k (Righta !(lz e))
  compile_lazy k (TCase sume (TLambda v1 e1) (TLambda v2 e2)) = do
    z <- mkvar "z"
    case1 <- compile_lazy k e1
    case2 <- compile_lazy k e2
    compile_lazy (Lambda z (Case (Var z) (Lambda v1 case1) (Lambda v2 case2))) sume
  compile_lazy k (TIf cond th el) = 
    compile_lazy k (TCase cond (TLambda !(mkvar "u") el) (TLambda !(mkvar "u") th))


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

prg4_il : il_expr
prg4_il = Case (Righta (Const 2)) 
            (Lambda "x" (Arith Add (Var "x") (Const 5)))
            (Lambda "y" (Arith Mul (Var "y") (Const 5)))

typeCheckIL : il_expr -> List String
typeCheckIL e = case the (Either String (ILType, Ctx)) $ run $ infer_ilt empty e of
                  Left err => [err]
                  Right (t, ctx) => map show $ Data.SortedMap.toList ctx


prg2_types : List String
prg2_types = typeCheckIL prg2_il

prg5 : Term
prg5 = TIf ((TConst 12) <@ (TConst 70)) 
             (TConst 1) 
             (TConst 20)

prg5_il : il_expr
prg5_il = runPure $ compile_lazy Stop prg5

--

rootSharp : String -> String -> String
rootSharp exp resTy = unwords $ intersperse "\n" ["Thunk fmain = " ++ exp ++ ";",
            "try",
            "{", 
               "while(true) {",
                 "fmain = fmain();",
               "}",
            "} catch (Res<"++resTy++"> r)",
            "{",
                "Console.WriteLine(\"result: {0}\", r.res);",
            "}"]

resultType : Ctx -> String
resultType ctx = case lookup Stop ctx of
                   Nothing => "lost result type"
                   Just sty => argTy sty

mkSharp : il_expr -> Either String String
mkSharp e = case the (Either String (ILType, Ctx)) $ run $ infer_ilt empty e of
              Left err => Left err
              Right (ty, ctx) => 
                let res = do mainExp <- genSharp (Data.SortedMap.toList ctx) e
                             defs <- get
                             let resTy = resultType ctx
                             pure $ (unwords $ intersperse "\n" (reverse defs)) ++ rootSharp mainExp resTy
                in the (Either String String) $ run res

phi : Either String String -> String
phi (Left s) = s
phi (Right s) = s

main : IO ()
main = putStrLn $ phi $ mkSharp prg5_il
