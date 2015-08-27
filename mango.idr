module Main
import Control.IOExcept
import Effect.State
import Effect.Exception
import Effect.StdIO
import SortedMap
import Debug.Trace

data Op = Add | Sub | Mul | Eql | Less | Mod
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
             | AMake il_expr                 -- new int[a]
             | AGet il_expr il_expr          -- a[b]
             | ASet il_expr il_expr il_expr  -- a[b] := c

instance Eq Op where
  Add == Add = True
  Sub == Sub = True
  Mul == Mul = True
  Eql == Eql = True
  Less == Less = True
  Mod == Mod = True
  _ == _ = False

instance Show Op where
  show Add = "+"
  show Sub = "-"
  show Mul = "*"
  show Eql = "="
  show Less = "<"
  show Mod = "%"

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
  (AMake a1) == (AMake a2) = a1 == a2
  (AGet a1 b1) == (AGet a2 b2) = a1 == a2 && b1 == b2
  (ASet a1 b1 c1) == (ASet a2 b2 c2) = a1 == a2 && b1 == b2 && c1 == c2
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
  show (AMake a) = "new int[" ++ show a ++ "]"
  show (AGet a b) = show a ++ "[" ++ show b ++ "]"
  show (ASet a b c) = show a ++ "[" ++ show b ++ "] := " ++ show c

instance Ord il_expr where
  compare a b = compare (show a) (show b)

mutual 
  data rt_val = VInt Int | VUnit | VPair rt_val rt_val | VCont name il_expr Env | VStop
              | VLeft rt_val | VRight rt_val | VArray (SortedMap Int Int)

  Env : Type
  Env = List (name, rt_val)

instance Show rt_val where
  show (VInt n) = show n
  show VUnit = "()"
  show (VPair a b) = "(" ++ show a ++ ", " ++ show b ++ ")"
  show (VCont x e env) = "(\\" ++ x ++ " => ...)" 
  show VStop = "Stop"
  show (VLeft v) = "Left " ++ show v
  show (VRight v) = "Right " ++ show v
  show (VArray m) = show $ SortedMap.toList m

RtVal : Type
RtVal = Either String rt_val 

raise_ : String -> RtVal
raise_ s = Left s 

getv : Env -> name -> RtVal
getv env var with (lookup var env)
  | Just v = pure v
  | Nothing = raise_ $ "unknown var " ++ var

doArith : Op -> rt_val -> rt_val -> RtVal
doArith Add (VInt a) (VInt b) = pure $ VInt (a + b)
doArith Sub (VInt a) (VInt b) = pure $ VInt (a - b)
doArith Mul (VInt a) (VInt b) = pure $ VInt (a * b)
doArith Mod (VInt a) (VInt b) = pure $ VInt (a `mod` b)
doArith Eql (VInt a) (VInt b) = pure $ if a == b then VRight VUnit else VLeft VUnit
doArith Less (VInt a) (VInt b) = pure $ if a < b then VRight VUnit else VLeft VUnit
doArith _ _ _ = raise_ "bad args in Arith"

eval_il : Env -> il_expr -> RtVal 
eval_il env (Var v) = getv env v
eval_il env (Const n) = return $ VInt n 
eval_il env Unit = return VUnit
eval_il env (Pair e1 e2) =  [| VPair (eval_il env e1) (eval_il env e2) |]
eval_il env (Fst e) = do
  case !(eval_il env e) of
    VPair a b => return a
    _ => raise_ "not a pair in Fst"
eval_il env (Snd e) = do
  case !(eval_il env e) of
    VPair a b => return b
    _ => raise_ "not a pair in Snd"
eval_il env (Lambda v e) = return $ VCont v e env
eval_il env (RecLambda f v e) = return k where k = VCont v e ((f,k)::env)
eval_il env (RunCont ef ex) = raise_ "trying to eval runcont"
eval_il env (Arith op e1 e2) = doArith op !(eval_il env e1) !(eval_il env e2) 
eval_il env Stop = return VStop
eval_il env (Lefta e) = pure $ VLeft !(eval_il env e)
eval_il env (Righta e) = pure $ VRight !(eval_il env e)
eval_il env (Case e (Lambda x1 e1) (Lambda x2 e2)) =
  case !(eval_il env e) of
    VLeft v  => eval_il ((x1, v)::env) e1
    VRight v => eval_il ((x2, v)::env) e2
    _ => raise_ "Not a sum type value in Case"
eval_il env (Case _ _ _) = raise_ "Err: Case with not Lambdas"    
eval_il env (AMake e) = 
  case !(eval_il env e) of
    VInt n => return $ VArray (insert (n-1) 0 empty)
    _ => raise_ "not an Int in AMake"
eval_il env (AGet a i) =
  case (!(eval_il env a), !(eval_il env i)) of
    (VArray m, VInt n) => case lookup n m of
                            Nothing => return $ VInt 0 --raise_ ("AGet out of bounds: " ++ show n)
                            Just v => return $ VInt v
    _ => raise_ "type mismatch in AGet"
eval_il env (ASet a i e) =
  case (!(eval_il env a), !(eval_il env i), !(eval_il env e)) of
    (VArray m, VInt n, VInt v) => return $ VArray (insert n v m)
    _ => raise_ "type mismatch in ASet"
                          

run_il : Env -> il_expr -> RtVal
run_il env (RunCont ef ex) = do
  vf <- eval_il env ef
  vx <- eval_il env ex
  case vf of
    VCont n e env0 => run_il ((n,vx)::env0) e
    --VCont n e env0 => let recur = trace ("run " ++ n ++ "=" ++ show vx) (\qq => do run_il ((n,vx)::env0) e)
    --                  in recur () 
    VStop => return vx
    _ => raise_ "bad fun_expr in RunCont"
run_il env (Case e (Lambda x1 e1) (Lambda x2 e2)) =
  case !(eval_il env e) of
    VLeft v  => run_il ((x1, v)::env) e1
    VRight v => run_il ((x2, v)::env) e2
    _ => raise_ "run_il: not a sum in case"
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
    AMake a => AMake (subst var sub a)
    AGet a b => AGet (subst var sub a) (subst var sub b)
    ASet a b c => ASet (subst var sub a) (subst var sub b) (subst var sub c)

                        
data ILType = IInt | IUnit | IPair ILType ILType | INot ILType | ITypeVar Int | IFalse 
            | ISum ILType ILType | IArray

instance Show ILType where
  show IInt = "Int"
  show IUnit = "Unit"
  show (IPair t1 t2) = "(" ++ show t1 ++", " ++ show t2 ++ ")"
  show (INot t) = "-" ++ show t
  show (ITypeVar n) = "t" ++ show n
  show IFalse = "0"
  show (ISum t1 t2) = "{" ++ show t1 ++ " | " ++ show t2 ++ "}"
  show IArray = "Int[]"

Ctx : Type
Ctx = SortedMap il_expr ILType

instance Show Ctx where
  show ctx = show $ SortedMap.toList ctx

freshTyVar : { [STATE Int] } Eff ILType
freshTyVar = do vn <- get
                put (vn + 1)
                pure $ ITypeVar vn

total
tysub : Int -> ILType -> ILType -> ILType
tysub v sub (ITypeVar n) = if n == v then sub else ITypeVar n
tysub v sub (IPair t1 t2) = IPair (tysub v sub t1) (tysub v sub t2)
tysub v sub (INot t) = INot (tysub v sub t)
tysub v sub (ISum t1 t2) = ISum (tysub v sub t1) (tysub v sub t2)
tysub v sub t = t

total
first2 : Vect (S (S n)) a -> (a,a)
first2 v = (head v, head $ tail v)

total tail2 : Vect (S (S n)) a -> Vect n a
tail2 v = tail $ tail v

-- => updated (context, additinal passed types)
unify : Ctx -> Vect n ILType -> ILType -> ILType -> {[EXCEPTION String]} Eff (Ctx, Vect n ILType)
unify ctx ts (ITypeVar v) t2 = pure $ trace ("tysub t" ++ show v ++ " -> " ++ show t2) $ 
                                 (map (tysub v t2) ctx, map (tysub v t2) ts)
--unify ctx (ITypeVar v) t2 = pure $ map (tysub v t2) ctx
--unify ctx t1 (ITypeVar v) = pure $ map (tysub v t1) ctx
unify ctx ts t1 (ITypeVar v) = pure $ trace ("tysub t" ++ show v ++ " -> " ++ show t1) $ 
                                (map (tysub v t1) ctx, map (tysub v t1) ts)
unify ctx ts (INot t1) (INot t2) = unify ctx ts t1 t2
unify ctx ts (IPair a1 a2) (IPair b1 b2) = do
  (ctx1, ts') <- unify ctx (a2 :: b2 :: ts) a1 b1
  let (a2', b2') = first2 ts'
  unify ctx1 (tail2 ts') a2' b2'
unify ctx ts IInt IInt = pure (ctx, ts)
unify ctx ts IUnit IUnit = pure (ctx, ts)
unify ctx ts IFalse IFalse = pure (ctx, ts)
unify ctx ts IArray IArray = pure (ctx, ts)
unify ctx ts (ISum a1 a2) (ISum b1 b2) = do
  (ctx1, ts') <- unify ctx (a2 :: b2 :: ts) a1 b1
  let (a2', b2') = first2 ts'
  unify ctx1 (tail2 ts') a2' b2'
unify ctx ts t1 t2 = raise $ "cannot unify " ++ show t1 ++ " and " ++ show t2

unify_ : Ctx -> ILType -> ILType -> {[EXCEPTION String]} Eff Ctx 
unify_ ctx t1 t2 = f () where
    f : () -> {[EXCEPTION String]} Eff Ctx 
    f = trace ("unify " ++ show t1 ++ " and " ++ show t2) (\x => do (cx,_) <- unify ctx [] t1 t2
                                                                    pure cx  
                                                          )

total
opResTy : Op -> ILType
opResTy Add = IInt
opResTy Sub = IInt
opResTy Mul = IInt
opResTy Mod = IInt
opResTy Eql = ISum IUnit IUnit
opResTy Less = ISum IUnit IUnit

defType : il_expr -> ILType -> Ctx -> Ctx
defType expr ty ctx = trace ("def " ++ show expr ++ " : " ++ show ty) $ insert expr ty ctx

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
                             let ctx' = defType expr tvar ctx
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
      ctx4 <- unify_ ctx3 t1 (INot t2) ---
      pure (IFalse, ctx4)
    RecLambda f v exp => do -- exp may have Var f
      (_, ctx1) <- infer_ilt ctx exp
      (tv, ctx2) <- infer_ilt ctx1 (Var v)
      (tf, ctx3) <- infer_ilt ctx2 (Var f)
      ctx4 <- unify_ ctx3 (INot tv) tf ---
      case lookup (Var f) ctx4 of
        Just t => pure (t, insert expr t ctx4)
        Nothing => raise "oops, Var f shoulda been in ctx4"
    Pair e1 e2 => do
      (t1, ctx1) <- infer_ilt ctx e1
      (t2, ctx2) <- infer_ilt ctx1 e2
      let ty = IPair t1 t2
      let ctx3 = insert expr ty ctx2
      pure (ty, ctx3)
    Fst e => do
      (te, ctx1) <- infer_ilt ctx e
      case te of 
        IPair t1 t2 => pure (t1, insert expr t1 ctx1)
        ITypeVar v => do
          t1 <- freshTyVar
          t2 <- freshTyVar
          let tp = IPair t1 t2
          ctx2 <- unify_ ctx1 te tp  ---
          pure (t1, insert expr t1 ctx2)
        _ => raise $ "pair type expected for " ++ show e ++ ", instead found " ++ show te
    Snd e => do
      (te, ctx1) <- infer_ilt ctx e
      case te of 
        IPair t1 t2 => pure (t2, insert expr t2 ctx1)
        ITypeVar v => do
          t1 <- freshTyVar
          t2 <- freshTyVar
          let tp = IPair t1 t2
          ctx2 <- unify_ ctx1 te tp   ---
          pure (t2, insert expr t2 ctx2)
        _ => raise $ "pair type expected for " ++ show e ++ ", instead found " ++ show te
    Arith op e1 e2 => do
      (t1, ctx1) <- infer_ilt ctx e1
      (t2, ctx2) <- infer_ilt ctx1 e2
      ctx3 <- unify_ ctx2 t1 IInt   ---
      ctx4 <- unify_ ctx3 t2 IInt   ---
      pure (opResTy op, ctx4)
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
        (INot ty1, INot ty2) => do 
          ctx3 <- unify_ ctx2 t0 (ISum ty1 ty2)   ---
          pure (IFalse, ctx3)
        _ => raise "Not lambda types found in case"
    AMake a => do
      (t, ctx1) <- infer_ilt ctx a
      ctx2 <- unify_ ctx1 t IInt
      pure (IArray, ctx2)
    AGet a b => do
      (ta, ctx1) <- infer_ilt ctx a
      (tb, ctx2) <- infer_ilt ctx1 b
      ctx3 <- unify_ ctx2 ta IArray
      ctx4 <- unify_ ctx3 tb IInt
      pure (IInt, ctx4)
    ASet a b c => do
      (ta, ctx1) <- infer_ilt ctx a
      (tb, ctx2) <- infer_ilt ctx1 b
      (tc, ctx3) <- infer_ilt ctx2 c
      ctx4 <- unify_ ctx3 ta IArray
      ctx5 <- unify_ ctx4 tb IInt
      ctx6 <- unify_ ctx5 tc IInt
      pure (IArray, ctx6)

                     
total showCtx : Ctx -> String
showCtx ctx = show $ SortedMap.toList ctx

total
tySharp : ILType -> String
tySharp IInt = "int"
tySharp IUnit = "Unit"
tySharp (IPair a b) = "Pair<" ++ tySharp a ++ ", " ++ tySharp b ++ ">"
tySharp (INot t) = "Kont<" ++ tySharp t ++ ">"
tySharp IFalse = " Err: 0 type "
tySharp (ITypeVar n) = " Err: unresolved type var t" ++ show n
tySharp (ISum a b) = "Sum<" ++ tySharp a ++ ", " ++ tySharp b ++ ">"
tySharp IArray = "int[]"

addDef : ILType -> String -> {[STATE (List String)]} Eff String
addDef ty s = do xs <- get
                 let f = "f" ++ show (length xs) 
                 put $ (tySharp ty ++ " " ++ f ++ " = " ++ s ++ ";") :: xs
                 return f

--Ctx2 : Type
--Ctx2 = List (il_expr, ILType)

total argTy : ILType -> String
argTy (INot t) = tySharp t
argTy t = "Err: argTy for positive type " ++ show t

--total
genSharp : Ctx -> il_expr -> { [EXCEPTION String] } Eff String
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
genSharp ctx (RecLambda f v e) = 
  let exp = RecLambda f v e in
  case lookup exp ctx of
    Nothing =>  raise $ "Err: unknown type for " ++ show exp ++ " ::: " ++ show ctx
    Just (INot ty) => pure $ "unrec<" ++ tySharp ty ++ ">((" 
                               ++ v ++ "," ++ f ++ ") => " ++ !(genSharp ctx e) ++ ")"
    Just ty => raise $ "RecLambda type shoulda been INot x, instead got " ++ show ty
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
genSharp ctx (AMake a) = pure $ "new int[" ++ !(genSharp ctx a) ++ "]"
genSharp ctx (AGet a i) = pure $ !(genSharp ctx a) ++ "[" ++ !(genSharp ctx i) ++ "]"
genSharp ctx (ASet a i v) = pure $ "set(" ++ !(genSharp ctx a) ++","++ !(genSharp ctx i) 
                             ++","++  !(genSharp ctx v) ++ ")"

data Term = TVar name | TConst Int | TUnit | TLambda name Term | TApply Term Term
             | TPair Term Term | TFst Term | TSnd Term | TArith Op Term Term
             | TLeft Term | TRight Term | TCase Term Term Term
             | TIf Term Term Term
             | TRecLambda name name Term   -- \ f x body
             | TAMake Term
             | TAGet Term Term
             | TASet Term Term Term
             | TLet name Term Term -- let nm = a in b

infixr 7 =@
(=@) : Term -> Term -> Term
a =@ b = TArith Eql a b

infixr 7 <@
(<@) : Term -> Term -> Term
a <@ b = TArith Less a b

tmod : Term -> Term -> Term
tmod a b = TArith Mod a b

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
  compile_lazy k (TRecLambda f arg expr) = do
    w <- mkvar "w"
    r <- mkvar "rec"
    u <- mkvar "u"
    exp <- compile_lazy (Snd (Var w)) expr 
    let exp2 = subst f (Lambda u (RunCont (Var u) (Var r))) $ subst arg (Fst(Var w)) exp
    return $ RunCont k (RecLambda r w exp2)
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
  compile_lazy k (TAMake n) = do
    sz <- mkvar "sz"
    compile_lazy (Lambda sz (RunCont k (AMake (Var sz)))) n
  compile_lazy k (TAGet a i) = do
    va <- mkvar "m"
    vi <- mkvar "i"
    compile_lazy 
      (Lambda va !(compile_lazy
                    (Lambda vi (RunCont k (AGet (Var va) (Var vi)))) 
                    i)) 
      a
  compile_lazy k (TASet a i v) = do
    va <- mkvar "m"
    vi <- mkvar "i"
    vv <- mkvar "v"
    compile_lazy 
      (Lambda va !(compile_lazy
                    (Lambda vi !(compile_lazy 
                                  (Lambda vv (RunCont k (ASet (Var va) (Var vi) (Var vv))))
                                  v) ) 
                    i))
      a
  compile_lazy k (TLet v wat were) = compile_lazy k (TApply (TLambda v were) wat)

typeCheckIL : il_expr -> List String
typeCheckIL e = case the (Either String (ILType, Ctx)) $ run $ infer_ilt empty e of
                  Left err => [err]
                  Right (t, ctx) => map show $ SortedMap.toList ctx

mkil : Term -> il_expr
mkil prg = runPure $ compile_lazy Stop prg

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
                let res = do mainExp <- genSharp ctx e
                             pure $ rootSharp mainExp (resultType ctx)
                in the (Either String String) $ run res

phi : Either String String -> String
phi (Left s) = s
phi (Right s) = s

compileAndGen : Term -> String
compileAndGen prg = phi . mkSharp $ mkil prg

implicit tvar : String -> Term
tvar nm = TVar nm

instance Num Term where
  (+) = TArith Add
  (-) = TArith Sub
  (*) = TArith Mul
  abs x = x
  fromInteger x = TConst (fromInteger x)

-------------------------------------
--external vars: 
-- code : int[]
-- email : int[]
-- elen : int = email.length

row1 : List Int
row1 = [0x67, 0xda, 0x9c, 0x87, 0x9c, 0x6a, 0x42, 0xd7, 0x9e, 0x16, 0x47, 0xf1, 0xd1, 0x73, 0xef, 0x45]

matrow : Term
matrow = foldl f (TAMake 16) (zip row1 [(the Int 0)..15] refl) where
          f m (x,i) = TASet m (TConst i) (TConst x) 

emloop : Term
emloop = TRecLambda "emloop" "i"
          (TLet "p" (((TAGet "matrow" "i") * (TAGet "email" ("i" `tmod` "elen"))) `tmod` 256)
            (TIf ("i" =@ 15) "p" ("p" + (TApply "emloop" ("i" + 1))))
            ) 

calccode : Term
calccode = TLet "matrow" matrow (TApply emloop 0)

prg_hex : Term
prg_hex = TLet "fromHex"  (TLambda "x" (TIf ("x" <@ 60) ("x" - 48) ("x" - 55)))
              ((TApply "fromHex" (TAGet "code" 3)) * 256 + 
               (TApply "fromHex" (TAGet "code" 4)) * 16 +
               (TApply "fromHex" (TAGet "code" 5))) 

main : IO ()
{-main = do traverse_ putStrLn $ typeCheckIL prg7_il
          let r = the (Either String rt_val) $ run_il [] prg7_il
          case r of
            Left err => putStrLn err
            Right v => print v-}

main = putStrLn $ compileAndGen calccode
--main = print $ run_il [] prg6_il
