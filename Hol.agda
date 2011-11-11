module Hol where

open import Data.String
open import Data.Nat
open import Data.Vec
open import Data.Bool
open import Data.AVL.Sets

record TypeOperator : Set where
  field name  : String
        arity : ℕ

data Type : Set where
  TyVar : String -> Type
  TyApp : (op : TypeOperator) -> Vec Type (TypeOperator.arity op) -> Type

fun_tyop : TypeOperator
fun_tyop = record { name = "->"; arity = 2 }
infixr 30 _⇒_
_⇒_     : Type -> Type -> Type
t1 ⇒ t2 = TyApp fun_tyop (t1 ∷ [ t2 ])

bool_tyop : TypeOperator
bool_tyop = record { name = "bool"; arity = 0 }
bool : Type
bool = TyApp bool_tyop []

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

α : Type
α = TyVar "A"

equality : Constant
equality = record { name = "="; type = α ⇒ α ⇒ bool }

-- substitutions
-- inst_type
-- (inst)

-- data Thm : ⟨Set⟩ Formula -> Formula where
--  Assume : ∀ t -> Thm (singleton t) t