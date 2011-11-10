module Hol where

open import Data.String
open import Data.Nat
open import Data.Vec
open import Data.Bool

record TypeOperator : Set where
  field name  : String
        arity : ℕ

data Type : Set where
  TyVar : String -> Type
  TyApp : (op : TypeOperator) -> Vec Type (TypeOperator.arity op) -> Type

fun_tyop : TypeOperator
fun_tyop = record { name = "->"; arity = 2 }
_⇒_     : Type -> Type -> Type
t1 ⇒ t2 = TyApp fun_tyop (t1 ∷ [ t2 ])

bool_tyop : TypeOperator
bool_tyop = record { name = "bool"; arity = 0 }
bool : Type
bool = TyApp bool_tyop []

record Constant : Set where
  field name : String
        type : Type

data Term : {_ : Type} -> {_ : Bool} -> Set where
  Var   : String -> (t : Type) -> Term {t} {true}
  Const : (c : Constant) -> Term {Constant.type c} {false}
  App   : ∀ {x} {y} {b1} {b2} -> Term {x ⇒ y} {b1} -> Term {x} {b2} -> Term {y} {false}
  Abs   : ∀ {x} {y} {b} -> Term {x} {true} -> Term {y} {b} -> Term {x ⇒ y} {false}

-- Formula : Bool -> Set
-- Formula = Term bool

-- data Thm : Formula -> FinSet Formula where