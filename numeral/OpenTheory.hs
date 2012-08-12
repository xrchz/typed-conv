module OpenTheory where
import Data.Map (Map)
import qualified Data.Map as Map (empty,lookup,size,insert,delete)
import qualified Data.List as List (map,intercalate)
import Data.Maybe (fromJust)
import Data.Char (isDigit)
import Control.Monad.Error (throwError,catchError)
import Control.Monad.State (StateT,get,put,liftIO,evalState)
import System.IO (Handle,IOMode(WriteMode),hPutStr,hPutStrLn,hGetLine)
import Prelude hiding (log,map,getLine)

-- subs n (x = y) (|- l = r[x]) = |- l = r[y]
-- assumes x is the nth operand of r
subs n eq th = trans th (build n (rhs (concl th))) where
  build 0 _ = eq
  build n (AppTerm f x) = AppThm (Refl f) (build (n-1) x)

mkns ns s = Name (ns, s)
minns  = mkns []
numns  = mkns ["Number","Natural"]
boolns = mkns ["Data","Bool"]

mkty op as = OpType (TypeOp op) as
fn x y = mkty (minns "->")      [x, y]
bool   = mkty (minns "bool")    []
num    = mkty (numns "natural") []

eq_tm ty = ConstTerm (Const (minns "=")) (fn ty (fn ty bool))
eq ty l r = AppTerm (AppTerm (eq_tm ty) l) r
eqn = eq num

rator (AppTerm f _) = f
rator tm = error ("rator " ++ show tm)
rand (AppTerm _ x) = x
rand tm = error ("rand " ++ show tm)
rhs = rand

truth = ConstTerm (Const (boolns "T")) bool

forall_tm ty = ConstTerm (Const (boolns "!")) (fn (fn ty bool) bool)
forall v@(Var (_,ty)) bod = AppTerm (forall_tm ty) (AbsTerm v bod)

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

alpha_nm = Name ([],"A")
alpha = VarType alpha_nm

type Component = String
type Namespace = [Component]
newtype Name = Name (Namespace, Component)
  deriving (Eq, Ord)

newtype TypeOp = TypeOp Name
  deriving (Eq, Ord)

newtype Var = Var (Name, Type)
  deriving (Eq, Ord)

data Term =
    AbsTerm Var Term
  | AppTerm Term Term
  | ConstTerm Const Type
  | VarTerm Var
  deriving (Eq, Ord)

data Proof =
    Refl Term
  | AppThm Proof Proof
  | AbsThm Var Proof
  | EqMp Proof Proof
  | Axiom Term
  | BetaConv Term
  | InstA Type Proof

trans th1 th2 = EqMp (AppThm (Refl t) th2) th1
  where t = rator (concl th1)

sym th = EqMp lel_rel lel
  where
    lel_rel = AppThm le_re lel
    lel = Refl l
    le_re = AppThm (Refl e) ler
    AppTerm (AppTerm e l) r = concl th
    ler = th

spec tm th = EqMp (sym pv_T) (Axiom truth)
  where
    pv_T = trans pv_lxPxv (trans lxPxv_lxTv lxTv_T)
    pv_lxPxv = sym (BetaConv lxPxv) -- P[v] = (\x. P[x]) v
    lxTv_T = BetaConv lxTv -- (\x. T) v = T
    AppTerm (AppTerm _ lxPxv) lxTv = concl lxPxv_lxTv
    lxPxv_lxTv = AppThm lxPx_lxT (Refl v) -- (\x. P[x]) v = (\x. T) v
    lxPx_lxT = EqMp bc lPP_lxTlxPx    -- (\x. P[x]) = (\x. T)
    bc = BetaConv (concl lPP_lxTlxPx) -- (\P. P = (\x. T)) (\x. P[x]) = (\x. P[x]) = (\x. T)
    lPP_lxTlxPx = EqMp faxPx_ fa_lxPx -- (\P. P = (\x. T)) (\x. P[x])
    faxPx_ = (AppThm fa_lPP_lxT (Refl lxPx)) -- (!x. P[x]) = (\P. P = (\x. T)) (\x. P[x])
    lxPx = rand (concl th)            -- (\x. P[x])
    fa_lPP_lxT = InstA ty forall_def  -- (!) = (\P. P = (\x. T))
    fa_lxPx = th                      -- !x. P[x]
    ty = tyof v
    v = tm

concl (Refl t) = eq (tyof t) t t
concl (AppThm th1 th2) = eq ty (AppTerm f1 x1) (AppTerm f2 x2)
  where (AppTerm (AppTerm _ f1) f2) = concl th1
        (AppTerm (AppTerm _ x1) x2) = concl th2
        (OpType _ [_,ty]) = tyof f1
concl (AbsThm v th) = eq ty (AbsTerm v t1) (AbsTerm v t2)
  where (AppTerm (AppTerm _ t1) t2) = concl th
        (Var (_,tyv)) = v
        ty = fn tyv (tyof t1)
concl (EqMp th1 th2) = rhs (concl th1)
concl (Axiom t) = t
concl (BetaConv tm@(AppTerm (AbsTerm v b) t)) = eq (tyof tm) tm (subst v t b)
concl (InstA ty th) = tminstA ty (concl th)

subst v t tm@(VarTerm v') = if v == v' then t else tm
subst _ _ tm@(ConstTerm _ _) = tm
subst v t (AppTerm t1 t2) = AppTerm (subst v t t1) (subst v t t2)
subst v t tm@(AbsTerm v' b) = if v == v' then tm else AbsTerm v' (subst v t b)

tyinstA t v@(VarType _) = if v == alpha then t else v
tyinstA t (OpType op args) = (OpType op (List.map (tyinstA t) args))
tminstA t tm = f tm
  where
    f (VarTerm (Var (v,ty))) = VarTerm (Var (v, g ty))
    f (ConstTerm c ty) = ConstTerm c (g ty)
    f (AppTerm t1 t2) = AppTerm (f t1) (f t2)
    f (AbsTerm (Var (v,ty)) tm) = AbsTerm (Var (v, g ty)) (f tm)
    g = tyinstA t

tyof (VarTerm (Var (_,ty))) = ty
tyof (ConstTerm _ ty) = ty
tyof (AppTerm f _) = r
  where OpType _ [_, r] = tyof f
tyof (AbsTerm (Var (_,x)) t) = fn x (tyof t)

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
  | ONum Int
  deriving (Eq, Ord)

data WriteState = WriteState {whandle :: Handle, wmap :: Map Object Int}

type WM a = StateT WriteState IO a

getField f = get >>= return . f

putWMap m = do
  s <- get
  put (s {wmap = m})

class Loggable a where
  key :: a -> Object
  log :: a -> WM ()

logRaw s = getField whandle >>= liftIO . flip hPutStr s
logRawLn s = getField whandle >>= liftIO . flip hPutStrLn s

logCommand = logRawLn

logNum = logCommand . (show :: Int -> String)

logComponent lr = lc where
  lc [] = return ()
  lc (x:xs) = do
    if elem x ".\"\\" then lr "\\" else return ()
    lr [x]
    lc xs

logNamespace lr = ln where
  ln [] = return ()
  ln (c:ns) = do
    lc c
    lr "."
    ln ns
  lc = logComponent logRaw

instance Loggable Name where
  key = OName
  log (Name (ns,n)) = do
    logRaw "\""
    logNamespace logRaw ns
    logComponent logRaw n
    logRawLn "\""

hc :: Loggable a => (a -> WM ()) -> a -> WM ()
hc log a = do
  m <- getField wmap
  case Map.lookup (key a) m of
    Just k -> do
      logNum k
      logCommand "ref"
    Nothing -> do
      log a
      m <- getField wmap
      let k = Map.size m
      logNum k
      logCommand "def"
      putWMap (Map.insert (key a) k m)

instance Loggable a => Loggable [a] where
  key = OList . (List.map key)
  log = hc l where
    l [] = logCommand "nil"
    l (x:xs) = do
      log x
      log xs
      logCommand "cons"

instance (Loggable a, Loggable b) => Loggable (a,b) where
  key (a,b) = OPair (key a, key b)
  log = hc l where
    l (a,b) = do
      log a
      log b
      logCommand "nil"
      logCommand "cons"
      logCommand "cons"

instance Loggable TypeOp where
  key = OTypeOp
  log = hc l where
    l (TypeOp t) = do
      log t
      logCommand "typeOp"

instance Loggable Type where
  key = OType
  log = hc l where
    l (OpType op args) = do
      log op
      log args
      logCommand "opType"
    l (VarType n) = do
      log n
      logCommand "varType"

instance Loggable Var where
  key = OVar
  log = hc l where
    l (Var (n,ty)) = do
      log n
      log ty
      logCommand "var"

instance Loggable Const where
  key = OConst
  log = hc l where
    l (Const c) = do
      log c
      logCommand "const"

instance Loggable Term where
  key = OTerm
  log = hc l where
    l (AbsTerm v t) = do
      log v
      log t
      logCommand "absTerm"
    l (AppTerm f x) = do
      log f
      log x
      logCommand "appTerm"
    l (ConstTerm c ty) = do
      log c
      log ty
      logCommand "constTerm"
    l (VarTerm v) = do
      log v
      logCommand "varTerm"

instance Loggable Proof where
  key = OThm . concl
  log = hc l where
    l (Refl tm) = do
      log tm
      logCommand "refl"
    l (Axiom tm) = do
      log ([]::[Term])
      log tm
      logCommand "axiom"
    l (EqMp th1 th2) = do
      log th1
      log th2
      logCommand "eqMp"
    l (AppThm th1 th2) = do
      log th1
      log th2
      logCommand "appThm"
    l (AbsThm v th) = do
      log v
      log th
      logCommand "absThm"
    l (BetaConv tm) = do
      log tm
      logCommand "betaConv"
    l (InstA ty th) = do
      log ([(alpha_nm,ty)],[]::[(Var,Term)])
      log th
      logCommand "subst"

logThm th = do
  log th
  log ([]::[Term])
  log (concl th)
  logCommand "thm"

instance Show Name where
  show (Name (ns,n)) = evalState c "" where
    c = (logComponent l n) >> get
    l s2 = get >>= (\s1 -> put (s1 ++ s2))

instance Show TypeOp where
  show (TypeOp n) = show n
data Type =
    OpType TypeOp [Type]
  | VarType Name
  deriving (Eq, Ord)
instance Show Type where
  show (VarType n) = show n
  show (OpType (TypeOp (Name ([],"->"))) [x,y]) = "("++(show x)++"->"++(show y)++")"
  show (OpType op args) = (List.intercalate " " (List.map show args))++(show op)

instance Show Var where
  show (Var(n,ty)) = "("++(show n)++":"++(show ty)++")"
newtype Const = Const Name
  deriving (Eq, Ord)
instance Show Const where
  show (Const n) = show n

instance Show Term where
  show (AbsTerm v b) = "(\\"++(show v)++". "++(show b)++")"
  show (AppTerm (AppTerm (ConstTerm (Const (Name([],"="))) _) l) r) = "("++(show l)++" = "++(show r)++")"
  show (AppTerm t1 t2) = "("++(show t1)++" "++(show t2)++")"
  show (ConstTerm c ty) = show c
  show (VarTerm v) = show v

data ReadState = ReadState {rhandle :: Handle, rmap :: Map Int Object, stack :: [Object]}

type RM a b = StateT (Either ReadState a) IO b

getStack :: RM a [Object]
getStack = do
  Left s <- get
  return $ stack s
putStack x = do
  Left s <- get
  put $ Left (s {stack = x})
putRMap m = do
  Left s <- get
  put $ Left (s {rmap = m})

getLine :: RM a String
getLine = do
  Left s <- get
  liftIO $ hGetLine (rhandle s)

-- in the absence of Data.DList...
empty = []
toList ls = ls
snoc ls x = ls ++ [x]

readName s = r s empty empty where
  r [] ns n = Name (toList ns, toList n)
  r ('\\':c:cs) ns n = r cs ns (snoc n c)
  r ('.':cs) ns n = r cs (snoc ns (toList n)) empty
  r (c:cs) ns n = r cs ns (snoc n c)

readTerm :: RM Term Term
readTerm = readArticle (\h c -> put (Right c)) (return . rand)

readArticle :: ([Term] -> Term -> RM a ()) -> (a -> RM a b) -> RM a b
readArticle axiom handleError = do
  l <- getLine
  case l of
    '"':s -> do
      stack <- getStack
      putStack $ OName (readName (init s)) : stack
    s@(c:cs) | isDigit c || c == '-' -> do
      stack <- getStack
      putStack $ ONum (read s) : stack
    "absTerm" -> do
      OTerm b : OVar v : stack <- getStack
      putStack $ OTerm (AbsTerm v b) : stack
    "appTerm" -> do
      OTerm x : OTerm f : stack <- getStack
      putStack $ OTerm (AppTerm f x) : stack
    "axiom" -> do
      OTerm c : OList h : _ <- getStack
      axiom (List.map (\(OTerm tm) -> tm) h) c
    "cons" -> do
      OList t : h : stack <- getStack
      putStack $ OList (h : t) : stack
    "const" -> do
      OName n : stack <- getStack
      putStack $ OConst (Const n) : stack
    "constTerm" -> do
      OType ty : OConst c : stack <- getStack
      putStack $ OTerm (ConstTerm c ty) : stack
    "def" -> do
      ONum k : x : stack <- getStack
      Left s <- get
      put $ Left (s {stack = x : stack, rmap = Map.insert k x (rmap s)})
    "nil" -> do
      stack <- getStack
      putStack $ OList [] : stack
    "opType" -> do
      OList ls : OTypeOp op : stack <- getStack
      putStack $ OType (OpType op (List.map strip ls)) : stack where
        strip (OType t) = t
    "pop" -> do
      x : stack <- getStack
      putStack stack
    "ref" -> do
      Left s <- get
      let ONum k : st = stack s
      put $ Left (s {stack = fromJust (Map.lookup k (rmap s)) : st})
    "remove" -> do
      Left s <- get
      let ONum k : st = stack s
      put $ Left (s {stack = fromJust (Map.lookup k (rmap s)) : st,
                     rmap = Map.delete k (rmap s)})
    "typeOp" -> do
      OName n : stack <- getStack
      putStack $ OTypeOp (TypeOp n) : stack
    "var" -> do
      OType ty : OName n : stack <- getStack
      putStack $ OVar (Var (n,ty)) : stack
    "varTerm" -> do
      OVar v : stack <- getStack
      putStack $ OTerm (VarTerm v) : stack
    "varType" -> do
      OName n : stack <- getStack
      putStack $ OType (VarType n) : stack
  s <- get
  case s of
    Right x -> handleError x
    _ -> readArticle axiom handleError

type Conv = Term -> Either String Proof
tryConv :: Conv -> Conv
tryConv c tm = catchError (c tm) (const (return (Refl tm)))
orElseConv :: Conv -> Conv -> Conv
orElseConv c1 c2 tm = catchError (c1 tm) (const (c2 tm))
depthConv :: Conv -> Conv
depthConv c = c `orElseConv` subConv (depthConv c)
subConv :: Conv -> Conv
subConv c = tryConv (appConv c `orElseConv` absConv c)
appConv :: Conv -> Conv
appConv c (AppTerm t1 t2) = do
  th1 <- tryConv c t1
  th2 <- tryConv c t2
  return (AppThm th1 th2)
appConv c _ = throwError "appConv"
absConv :: Conv -> Conv
absConv c (AbsTerm v tm) = do
  th <- tryConv c tm
  return (AbsThm v th)
absConv c _ = throwError "absConv"
