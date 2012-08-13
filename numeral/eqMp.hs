import qualified Data.Map as Map (empty)
import Data.Set (fromList)
import Control.Monad.State (liftIO,evalStateT)
import Control.Exception (throw)
import System.IO (stdin,stdout)
import OpenTheory

main = evalStateT c rs where
  c = do
    thms <- readArticle (\h c s -> putStack $ (OThm $ Axiom (fromList h) c) : s) defaultHandler thmsOnEOF
    liftIO $ evalStateT (output thms) ws where
      ws = WriteState {whandle=stdout, wmap=Map.empty}
      output [th1,th2] = logThm (EqMp th1 th2)
      output _ = error "didn't get exactly 2 theorems"
  rs = ReadState {rhandle=stdin, rmap=Map.empty, stack=[], thms=[]}
