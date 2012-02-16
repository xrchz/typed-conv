import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Map as Map (insert,lookup,size)
import Control.Monad.State (StateT,get,put,liftIO)
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

type M a = StateT (Map Object Int) IO a

class Loggable a where
  key :: a -> Object
  log :: a -> M ()

getMap = get
putMap = put

hc :: Loggable a => a -> M a
hc a = do
  m <- getMap
  case Map.lookup (key a) m of
    Just k -> do
      liftIO $ logNum k
      liftIO $ logCommand "ref"
    Nothing -> do
      log a
      m <- getMap
      let k = Map.size m
      liftIO $ logNum k
      liftIO $ logCommand "def"
      putMap (Map.insert (key a) k m)
  return a

mkns ns s = hc $ Name (ns, s)
minns  = mkns []
boolns = mkns ["Data","Bool"]
numns  = mkns ["Number","Natural"]

mTypeOp mn = do
  n <- mn
  hc $ TypeOp n

mOpType mop margs = do
  op <- mop
  args <- margs
  hc $ OpType op args

mVarType mn = do
  n <- mn
  hc $ VarType n

mConst mn = do
  n <- mn
  hc $ Const n

mConstTerm mc mty = do
  c <- mc
  ty <- mty
  hc $ ConstTerm c ty

mAppTerm mf mx = do
  f <- mf
  x <- mx
  hc $ AppTerm f x

mAbsTerm mx mb = do
  x <- mx
  b <- mb
  hc $ AbsTerm x b

fn mx my = do
  x <- mx
  y <- my
  mOpType (mTypeOp (minns "->")) (hc [x, y])

bool = mOpType (mTypeOp (boolns "bool")) (hc [])
num = mOpType (mTypeOp (numns "natural")) (hc [])
alpha_nm = hc $ Name ([],"A")
alpha = mVarType alpha_nm
eq_tm ty = mConstTerm (mConst (minns "=")) (fn ty (fn ty bool))
eq ty l r = mAppTerm (mAppTerm (eq_tm ty) l) r
eqn = eq num
rator (AppTerm (AppTerm f _) _) = f
rand (AppTerm _ r) = r
rhs = rand
forall_tm ty = mConstTerm (mConst (boolns "!")) (fn (fn ty bool) bool)

tyof (VarTerm (Var (_,ty))) = ty
tyof (ConstTerm _ ty) = ty
tyof (AppTerm f _) = r
  where OpType _ [_, r] = tyof f
tyof (AbsTerm (Var (_,x)) t) = fn x (tyof t)

forall mv mb = do
  v@(Var (_,ty)) <- mv
  bod <- mb
  mAppTerm (forall_tm (hc ty)) (mAbsTerm (hc v) bod)
truth = mConstTerm (mConst (boolns "T")) bool

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
trans th1 th2 = EqMp (AppThm (Refl t) th2) th1
  where t = rator (concl th1)
sym th = EqMp lel_rel lel
  where
    lel = Refl l
    lel_rel = AppThm ler el_el
    el_el = Refl (AppTerm (eq_tm ty) l)
    ty = tyof l
    AppTerm (AppTerm _ l) r = concl th
    ler = th
forall_def = Axiom
  (eq (fn (fn alpha bool) bool)
    (forall_tm alpha)
    (AbsTerm p
      (eq (fn alpha bool)
        (VarTerm p)
        (AbsTerm x truth))))
  where
    x = Var (Name ([],"x"),alpha)
    p = Var (Name ([],"P"),fn alpha bool)
spec tm th = EqMp (sym pv_T) (Axiom truth)
  where
    pv_T = trans pv_lxPxv (trans lxPxv_lxTv lxTv_T)
    pv_lxPxv = sym (BetaConv lxPxv)
    lxTv_T = BetaConv lxTv
    AppTerm (AppTerm _ lxPxv) lxTv = concl lxPxv_lxTv
    lxPxv_lxTv = AppThm lxPx_lxT (Refl v)
    lxPx_lxT = EqMp (BetaConv (concl lPP_lxTlxPx)) lPP_lxTlxPx
    lPP_lxTlxPx = EqMp (AppThm fa_lPP_lxT (Refl lxPx)) fa_lxPx
    lxPx = rand (concl th)
    fa_lPP_lxT = InstA ty forall_def
    fa_lxPx = th
    ty = tyof v
    v = tm
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
logNum = logCommand . show

bit_tm s = ConstTerm (Const (numns ("bit"++s))) (fn num num)
bit0_tm = bit_tm "0"
bit1_tm = bit_tm "1"
bit0 = AppTerm bit0_tm
bit1 = AppTerm bit1_tm
bit2 = AppTerm (bit_tm "2")
zero = ConstTerm (Const (numns "zero")) num
suc = AppTerm (ConstTerm (Const (numns "suc")) (fn num num))
nv = Var (Name ([],"n"),num)
n = VarTerm nv
th1 = Axiom (forall nv (eqn (bit2 n) (suc (bit1 n))))
th2 = Axiom (eqn (suc zero) (bit1 zero))
th3 = Axiom (forall nv (eqn (suc (bit0 n)) (bit1 n)))
th4 = Axiom (forall nv (eqn (suc (bit1 n)) (bit0 (suc n))))
data Norrish =
    NZero
  | NBit1 Norrish
  | NBit2 Norrish
n2t NZero = zero
n2t (NBit1 n) = bit1 (n2t n)
n2t (NBit2 n) = bit2 (n2t n)
data Binary =
    BZero
  | BBit0 Binary
  | BBit1 Binary
t2b tm = if tm == zero then BZero else
         if rator tm == bit0_tm then BBit0 (t2b (rand tm)) else
         if rator tm == bit1_tm then BBit1 (t2b (rand tm)) else error "t2b"
b2t BZero = zero
b2t (BBit0 b) = bit0 (b2t b)
b2t (BBit1 b) = bit1 (b2t b)
data Path = R
subs [] eq th = eq
subs (R:rs) eq th = AppThm (Refl f) (subs rs eq th)
  where (AppTerm f _) = concl th
binc BZero = th2
binc (BBit0 n) = spec (b2t n) th3
binc (BBit1 n) = subs [R,R] (binc n) (spec (b2t n) th4)
n2b NZero = Refl zero
n2b (NBit1 n) = AppThm (Refl bit1_tm) (n2b n)
n2b (NBit2 n) = trans (subs [R,R,R] (n2b n) (spec (n2t n) th1)) (binc nb)
  where nb = t2b (rhs (concl (n2b n)))
