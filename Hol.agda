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