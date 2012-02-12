type Name = ([String], String)
type TypeOp = Name
data Type =
    OpType TypeOp [Type]
  | VarType Name
  deriving (Eq, Show)
type Var = (Name, Type)
type Const = Name
data Term =
    AbsTerm Var Term
  | AppTerm Term Term
  | ConstTerm Const Type
  | VarTerm Var
  deriving (Eq, Show)
tyof (VarTerm (_,ty)) = ty
tyof (ConstTerm _ ty) = ty
tyof (AppTerm f x) = fn (tyof f) (tyof x)
tyof (AbsTerm (_,x) t) = fn x (tyof t)
rator (AppTerm (AppTerm f _) _) = f
lhs (AppTerm (AppTerm _ l) _) = l
rand (AppTerm _ r) = r
rhs = rand
truth = ConstTerm (boolns,"T") bool
alpha_nm = ([],"A")
alpha = VarType alpha_nm
boolns = ["Data","Bool"]
numns = ["Number","Natural"]
fn x y = OpType ([],"->") [x, y]
bool = OpType (boolns,"bool") []
num = OpType (numns,"natural") []
eq_tm ty = ConstTerm ([],"=") (fn ty (fn ty bool))
eq ty l r = AppTerm (AppTerm (eq_tm ty) l) r
eqn = eq num
forall_tm ty = ConstTerm (boolns,"!") (fn (fn ty bool) bool)
forall v@(_,ty) bod = AppTerm (forall_tm ty) (AbsTerm v bod)
forall_def = Axiom
  (eq (fn (fn alpha bool) bool)
    (forall_tm alpha)
    (AbsTerm p
      (eq (fn alpha bool)
        (VarTerm p)
        (AbsTerm x truth))))
  where
    x = (([],"x"),alpha)
    p = (([],"P"),fn alpha bool)
data Proof =
    Refl Term
  | AppThm Proof Proof
  | EqMp Proof Proof
  | Axiom Term
  | BetaConv Term
  | InstA Type Proof
  deriving Show
subst v t tm@(VarTerm v') = if v == v' then t else tm
subst _ _ tm@(ConstTerm _ _) = tm
subst v t (AppTerm t1 t2) = AppTerm (subst v t t1) (subst v t t2)
subst v t tm@(AbsTerm v' b) = if v == v' then tm else AbsTerm v' (subst v t b)
tyinstA t v@(VarType _) = if v == alpha then t else v
tyinstA t (OpType op args) = (OpType op (map (tyinstA t) args))
tminstA t tm = f tm
  where
    f (VarTerm (v,ty)) = VarTerm (v, g ty)
    f (ConstTerm c ty) = ConstTerm c (g ty)
    f (AppTerm t1 t2) = AppTerm (f t1) (f t2)
    f (AbsTerm (v,ty) tm) = AbsTerm (v, g ty) (f tm)
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
bit_tm s = ConstTerm (numns,"bit"++s) (fn num num)
bit0_tm = bit_tm "0"
bit1_tm = bit_tm "1"
bit0 = AppTerm bit0_tm
bit1 = AppTerm bit1_tm
bit2 = AppTerm (bit_tm "2")
zero = ConstTerm (numns,"zero") num
suc = AppTerm (ConstTerm (numns,"suc") (fn num num))
nv = (([],"n"),num)
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
-- import Data.Map (Map)
-- import qualified Data.Map as Map
-- import Control.Monad.State
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
log_proof (InstA ty th) = do
  log_subst ([(alpha_nm,ty)],[])
  log_proof th
  log_command "subst"
