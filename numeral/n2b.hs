import Data.Set (Set)
import Data.Map (Map)
import Prelude hiding (log)
type Component = String
type Namespace = [Component]
newtype Name = Name (Namespace, Component)
  deriving (Eq, Ord)
newtype TypeOp = TypeOp Name
  deriving (Eq, Ord)
data Type =
    OpType TypeOp [Type]
  | VarType Name
  deriving (Eq, Ord)
newtype Var = Var (Name, Type)
  deriving (Eq, Ord)
newtype Const = Const Name
  deriving (Eq, Ord)
data Term =
    AbsTerm Var Term
  | AppTerm Term Term
  | ConstTerm Const Type
  | VarTerm Var
  deriving (Eq, Ord)
tyof (VarTerm (Var (_,ty))) = ty
tyof (ConstTerm _ ty) = ty
tyof (AppTerm f _) = r
  where OpType _ [_, r] = tyof f
tyof (AbsTerm (Var (_,x)) t) = fn x (tyof t)
minns s = Name ([], s)
boolns s = Name (["Data","Bool"], s)
fn x y = OpType (TypeOp (minns "->")) [x, y]
alpha_nm = Name ([],"A")
alpha = VarType alpha_nm
bool = OpType (TypeOp (boolns "bool")) []
eq_tm ty = ConstTerm (Const (minns "=")) (fn ty (fn ty bool))
eq ty l r = AppTerm (AppTerm (eq_tm ty) l) r
rand (AppTerm _ r) = r
rhs = rand
data Object =
    OTerm Term
  | OType Type
  | OPair (Object, Object)
  | OList [Object]
  | OName Name
  | OConst Const
  | OVar Var
  | OTypeOp TypeOp
  | OThm Term
  deriving (Eq, Ord)
logRaw = putStr
logRawLn = putStrLn
logCommand = logRawLn
logNamespace [] = return ()
logNamespace (c:ns) = do
  logComponent c
  logRaw "."
  logNamespace ns
logComponent [] = return ()
logComponent (x:xs) = do
  if elem x ".\"\\" then logRaw "\\" else return ()
  logRaw [x]
  logComponent xs
class Loggable a where
  key :: a -> Object
  log :: a -> IO ()
instance Loggable Name where
  key = OName
  log (Name (ns,n)) = do
    logRaw "\""
    logNamespace ns
    logComponent n
    logRawLn "\""
instance Loggable Var where
  key = OVar
  log (Var (n,ty)) = do
    log n
    log ty
    logCommand "var"
instance Loggable Const where
  key = OConst
  log (Const c) = log c
instance Loggable TypeOp where
  key = OTypeOp
  log (TypeOp t) = log t
instance Loggable a => Loggable [a] where
  key = OList . (map key)
  log [] = logCommand "nil"
  log (x:xs) = do
    log x
    log xs
    logCommand "cons"
instance Loggable Type where
  key = OType
  log (OpType op args) = do
    log op
    log args
    logCommand "opType"
  log (VarType n) = do
    log n
    logCommand "varType"
instance Loggable Term where
  key = OTerm
  log (AbsTerm v t) = do
    log v
    log t
    logCommand "absTerm"
  log (AppTerm f x) = do
    log f
    log x
    logCommand "appTerm"
  log (ConstTerm c ty) = do
    log c
    log ty
    logCommand "constTerm"
  log (VarTerm v) = do
    log v
    logCommand "varTerm"
data Proof =
    Refl Term
  | AppThm Proof Proof
  | EqMp Proof Proof
  | Axiom Term
  | BetaConv Term
  | InstA Type Proof
subst v t tm@(VarTerm v') = if v == v' then t else tm
subst _ _ tm@(ConstTerm _ _) = tm
subst v t (AppTerm t1 t2) = AppTerm (subst v t t1) (subst v t t2)
subst v t tm@(AbsTerm v' b) = if v == v' then tm else AbsTerm v' (subst v t b)
tyinstA t v@(VarType _) = if v == alpha then t else v
tyinstA t (OpType op args) = (OpType op (map (tyinstA t) args))
tminstA t tm = f tm
  where
    f (VarTerm (Var (v,ty))) = VarTerm (Var (v, g ty))
    f (ConstTerm c ty) = ConstTerm c (g ty)
    f (AppTerm t1 t2) = AppTerm (f t1) (f t2)
    f (AbsTerm (Var (v,ty)) tm) = AbsTerm (Var (v, g ty)) (f tm)
    g = tyinstA t
concl (Refl t) = eq (tyof t) t t
concl (AppThm th1 th2) = eq ty (AppTerm f1 x1) (AppTerm f2 x2)
  where (AppTerm (AppTerm _ f1) f2) = concl th1
        (AppTerm (AppTerm _ x1) x2) = concl th2
        (OpType _ [_,ty]) = tyof f1
concl (EqMp th1 th2) = rhs (concl th1)
concl (Axiom t) = t
concl (BetaConv (AppTerm (AbsTerm v tm) t)) = subst v t tm
concl (InstA ty th) = tminstA ty (concl th)
instance (Loggable a, Loggable b) => Loggable (a,b) where
  key (a,b) = OPair (key a, key b)
  log (a,b) = do
    log a
    log b
    logCommand "nil"
    logCommand "cons"
    logCommand "cons"
instance Loggable Proof where
  key = OThm . concl
  log (Refl tm) = do
    log tm
    logCommand "refl"
  log (Axiom tm) = do
    log tm
    logCommand "axiom"
  log (EqMp th1 th2) = do
    log th1
    log th2
    logCommand "eqMp"
  log (AppThm th1 th2) = do
    log th1
    log th2
    logCommand "appThm"
  log (BetaConv tm) = do
    log tm
    logCommand "betaConv"
  log (InstA ty th) = do
    log ([(alpha_nm,ty)],[]::[(Var,Term)])
    log th
    logCommand "subst"
logNum :: Int -> IO ()
logNum n = logCommand . show
type Dict = Map Object Int
data Logged a = Logged (Dict -> (Dict, IO a))
