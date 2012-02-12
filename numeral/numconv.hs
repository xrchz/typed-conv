type Name = ([String], String)
type TypeOp = Name
data Type =
    OpType TypeOp [Type]
  | VarType Name
  deriving (Eq, Show)
type Var = (Name, Type)
type Const = (Name, Type)
data Term =
    AbsTerm Var Term
  | AppTerm Term Term
  | ConstTerm Const
  | VarTerm Var
  deriving (Eq, Show)
tyof (VarTerm (_,ty)) = ty
tyof (ConstTerm (_,ty)) = ty
tyof (AppTerm f x) = fn (tyof f) (tyof x)
tyof (AbsTerm (_,x) t) = fn x (tyof t)
rator (AppTerm (AppTerm f _) _) = f
lhs (AppTerm (AppTerm _ l) _) = l
rand (AppTerm _ r) = r
rhs = rand
data Proof =
    Refl Term
  | Spec Term Proof
  | AppThm Proof Proof
  | EqMp Proof Proof
  | Axiom Term
  | BetaConv Term
  deriving Show
concl (Refl t) = eq (tyof t) t t
concl (Spec t th) = subst v t tm
  where (AbsTerm v tm) = rand (concl th)
concl (AppThm th1 th2) = eq ty (AppTerm f1 x1) (AppTerm f2 x2)
  where (AppTerm (AppTerm _ f1) f2) = concl th1
        (AppTerm (AppTerm _ x1) x2) = concl th2
        (OpType _ [_,ty]) = tyof f1
concl (EqMp th1 th2) = rhs (concl th1)
concl (Axiom t) = t
concl (BetaConv (AppTerm (AbsTerm v tm) t)) = subst v t tm
trans th1 th2 = EqMp (AppThm (Refl t) th2) th1
  where t = rator (concl th1)
boolns = ["Data","Bool"]
numns = ["Number","Natural"]
fn x y = OpType ([],"->") [x, y]
bool = OpType (boolns,"bool") []
num = OpType (numns,"natural") []
forall_tm ty = (ConstTerm ((boolns,"!"), fn (fn ty bool) bool))
forall v@(_,ty) bod = AppTerm (forall_tm ty) (AbsTerm v bod)
nv = (([],"n"),num)
n = VarTerm nv
eq ty l r =
  AppTerm
    (AppTerm (ConstTerm (([],"="), fn ty (fn ty bool))) l) r
eqn = eq num
subst v t tm@(VarTerm v') = if v == v' then t else tm
subst _ _ tm@(ConstTerm _) = tm
subst v t (AppTerm t1 t2) = AppTerm (subst v t t1) (subst v t t2)
subst v t tm@(AbsTerm v' b) = if v == v' then tm else AbsTerm v' (subst v t b)
bit_tm s = ConstTerm ((numns,"bit"++s), fn num num)
bit0_tm = bit_tm "0"
bit1_tm = bit_tm "1"
bit0 = AppTerm bit0_tm
bit1 = AppTerm bit1_tm
bit2 = AppTerm (bit_tm "2")
zero = ConstTerm ((numns,"zero"),num)
suc = AppTerm (ConstTerm ((numns,"suc"), fn num num))
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
binc (BBit0 n) = Spec (b2t n) th3
binc (BBit1 n) = subs [R,R] (binc n) (Spec (b2t n) th4)
n2b NZero = Refl zero
n2b (NBit1 n) = AppThm (Refl bit1_tm) (n2b n)
n2b (NBit2 n) = trans (subs [R,R,R] (n2b n) (Spec (n2t n) th1)) (binc nb)
  where nb = t2b (rhs (concl (n2b n)))
-- import Data.Map (Map)
-- import qualified Data.Map as Map
-- import Control.Monad.State
truth = ConstTerm ((boolns,"T"),bool)
alpha = VarType ([],"A")
p ty = (([],"P"),fn ty bool)
lxT ty = AbsTerm (([],"x"),ty) truth
forall_def_tm ty = AbsTerm (p ty) (eq (fn ty bool) (VarTerm (p ty)) (lxT ty))
forall_def = Axiom (eq (fn (fn alpha bool) bool) (forall_tm alpha) (forall_def_tm alpha))
log_alpha_subst ty = do
  --[[alpha,ty],[]]
  log_nil
  log_nil
  log_cons
  log_nil
  log_type ty
  log_cons
  log_type alpha
  log_cons
  log_cons
log_proof (Refl tm) = do
  log_term tm
  log_command "refl"
log_proof (Axiom tm) = do
  log_term tm
  log_command "axiom"
log_proof (EqMp th1 th2) = do
  log_proof th1
  log_proof th2
  log_command "eqMp"
log_proof (AppThm th1 th2) = do
  log_proof th1
  log_proof th2
  log_command "appThm"
log_proof (BetaConv tm) = do
  log_term tm
  log_command "betaConv"
log_proof (Spec tm th) = do
  c@(AbsTerm (_,ty) _) <- rand (concl th) -- c = \x. P x
  log_proof (Refl tm)
  -- |- v = v
  log_proof (BetaConv (AppTerm (forall_def_tm ty) c))
  -- |- (\P. P = \x. T) (\x. P x) = ((\x. P x) = \x. T)
  -- |- v = v
  log_alpha_subst ty
  log_command "subst"
  log_proof forall_def
  -- |- (!) = \P. P = \x. T
  -- |- (\P. P = \x. T) (\x. P x) = ((\x. P x) = \x. T)
  -- |- v = v
  log_proof (Refl c)
  -- |- (\x. P x) = (\x. P x) 
  -- |- (!) = \P. P = \x. T
  -- |- (\P. P = \x. T) (\x. P x) = ((\x. P x) = \x. T)
  -- |- v = v
  log_command "appThm"
  -- |- (!) (\x. P x) = (\P. P = \x. T) (\x. P x)
  -- |- (\P. P = \x. T) (\x. P x) = ((\x. P x) = \x. T)
  -- |- v = v
  log_proof th
  -- |- (!) (\x. P x)
  -- |- (!) (\x. P x) = (\P. P = \x. T) (\x. P x)
  -- |- (\P. P = \x. T) (\x. P x) = ((\x. P x) = \x. T)
  -- |- v = v
  log_command "eqMp"
  -- |- (\P. P = \x. T) (\x. P x)
  -- |- (\P. P = \x. T) (\x. P x) = ((\x. P x) = \x. T)
  -- |- v = v
  log_command "eqMp"
  -- |- (\x. P x) = \x. T
  -- |- v = v
  log_command "appThm"
  -- |- (\x. P x) v = (\x. T) v
  log_proof (BetaConv (AppTerm c tm))
  -- |- (\x. P x) v = P v
  -- |- (\x. P x) v = (\x. T) v
  log_proof (BetaConv (AppTerm (lxT ty) tm))
  -- |- (\x. T) v = T
  -- |- (\x. P x) v = P v
  -- |- (\x. P x) v = (\x. T) v
  appThm to get
  |- P v = T
  refl to get
  |- (=) = (=)
  appThm to get
  |- (=) P v = (=) T
  appThm to get
  |- P v = P v = T = P v
  eqMp to get
  |- T = P v
  eqMp to get
  |- P v
