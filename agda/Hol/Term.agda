module Hol.Term where

open import Hol.Type using (_str<_;Type;α;_⇒_;bool) renaming (_<_ to _ty<_)
open import Data.AVL.Sets using ()
open import Data.String using (String)

record Constant : Set where
  field name : String
        type : Type

record Variable : Set where
  field name : String
        type : Type

data Term : {_ : Type} -> Set where
  Var   : (v : Variable) -> Term {Variable.type v}
  Const : (c : Constant) -> Term {Constant.type c}
  App   : ∀ {x} {y} -> Term {x ⇒ y} -> Term {x} -> Term {y}
  Abs   : ∀ {y} -> (v : Variable) -> Term {y} -> Term {(Variable.type v) ⇒ y}

Formula : Set
Formula = Term {bool}

-- strict total order on terms?
-- alpha equivalence?

equality : Constant
equality = record { name = "="; type = α ⇒ α ⇒ bool }

-- substitutions
-- inst_type
-- (inst)

-- data Thm : ⟨Set⟩ Formula -> Formula where
--  Assume : ∀ t -> Thm (singleton t) t
