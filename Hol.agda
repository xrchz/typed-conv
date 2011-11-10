module Hol where

open import Data.String
open import Data.Nat
open import Data.Vec

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

data Term : Type -> Set where
  Var   : String -> (t : Type) -> Term t
  Const : (c : Constant) -> Term (Constant.type c)
  App   : ∀ {x} {y} -> Term (x ⇒ y) -> Term x -> Term y
  Abs   : ∀ {x} {y} -> Term x -> Term y -> Term (x ⇒ y)