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
p = (([],"P"),fn alpha bool)
forall_def = Axiom (eq (fn (fn alpha bool) bool) (forall_tm alpha) (AbsTerm p (eq (fn alpha bool) (VarTerm p) (AbsTerm (([],"x"),alpha) truth))))
{-
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
log_proof (Spec tm th) = do
  log_proof th
  c <- rand (concl th)
  log_proof (Refl c)
  log_command "appThm"

  want P v
  have |- (!) (\x. P x)            (th)
  have |- (!) = \P. P = \x. T      (!-def)
  have |- T
  appThm to get
  |- (\P. P = \x. T) (\x. P x)
  betaConv to get
  |- (\P. P = \x. T) (\x. P x) = ((\x. P x) = \x. T)
  eqMp to get
  |- (\x. P x) = \x. T
  appThm to get
  |- (\x. P x) v = (\x. T) v
  betaConv to get
  |- (\x. P x) v = P v
  betaConv to get
  |- (\x. T) v = T
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
-}
