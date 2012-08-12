import qualified Data.Map as Map (empty)
import Data.String (String)
import Control.Monad.State (liftIO,evalStateT)
import Control.Monad.Error (throwError)
import System.IO (stdin,stdout)
import Prelude hiding (getLine)
import OpenTheory

data Norrish =
    NZero
  | NBit1 Norrish
  | NBit2 Norrish

data Binary =
    BZero
  | BBit0 Binary
  | BBit1 Binary

-- n2b n[Nor] = |- n[Nor] = n[Bin]
n2b NZero = Refl zero
n2b (NBit1 n) = AppThm (Refl bit1_tm) (n2b n)
n2b (NBit2 n) = trans (subs 2 (n2b n) (spec (n2t n) th1)) (binc (BBit1 nb))
  where nb = t2b (rhs (concl (n2b n)))

-- binc n[Bin] = |- suc n[Bin] = (n+1)[Bin]
binc BZero = th2
binc (BBit0 n) = spec (b2t n) th3
binc (BBit1 n) = subs 1 (binc n) (spec (b2t n) th4)

th1 = Axiom (forall vn (eqn (bit2 n) (suc (bit1 n))))
th2 = Axiom (eqn (suc zero) (bit1 zero))
th3 = Axiom (forall vn (eqn (suc (bit0 n)) (bit1 n)))
th4 = Axiom (forall vn (eqn (suc (bit1 n)) (bit0 (suc n))))

vn = Var (Name ([],"n"),num)
n  = VarTerm vn

bit_tm s = ConstTerm (Const (numns ("bit"++s))) (fn num num)
bit0_tm = bit_tm "0"
bit1_tm = bit_tm "1"
bit2_tm = bit_tm "2"
bit0 = AppTerm bit0_tm
bit1 = AppTerm bit1_tm
bit2 = AppTerm bit2_tm

zero = ConstTerm (Const (numns "zero")) num
suc  = AppTerm (ConstTerm (Const (numns "suc")) (fn num num))

-- Norrish -> Term
n2t NZero = zero
n2t (NBit1 n) = bit1 (n2t n)
n2t (NBit2 n) = bit2 (n2t n)
-- Term -> Norrish
t2n :: Term -> Either String Norrish
t2n tm = if tm == zero then return NZero else
         case tm of
           (AppTerm f x) -> if f == bit1_tm then t2n x >>= (return . NBit1) else
                            if f == bit2_tm then t2n x >>= (return . NBit2) else
                            throwError "t2n"
           _ -> throwError "t2n"

-- Term -> Binary
t2b tm = if tm == zero then BZero else
         if rator tm == bit0_tm then BBit0 (t2b (rand tm)) else
         if rator tm == bit1_tm then BBit1 (t2b (rand tm)) else error "t2b"
-- Binary -> Term
b2t BZero = zero
b2t (BBit0 b) = bit0 (b2t b)
b2t (BBit1 b) = bit1 (b2t b)

main = evalStateT c rs where
  c = do
    tm <- readTerm
    liftIO $ evalStateT (output tm) ws where
      ws = WriteState {whandle=stdout, wmap=Map.empty}
      output tm =
        case depthConv ((flip (>>=) (return . n2b)) . t2n) tm of
          Right th -> logThm th
          Left err -> logRawLn err
  rs = Left $ ReadState {rhandle=stdin, rmap=Map.empty, stack=[]}
