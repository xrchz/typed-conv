open import Name using (Name)
module Hol.Term (Names : Name) where

import Hol.Type
open Hol.Type (Names) using (Type;α;_=>_;bool) renaming (_<_ to _ty<_)
open import Data.AVL.Sets using ()

String = Name.Carrier Names
_S<_ = Name._<_ Names
fromString = Name.fromString Names

record Constant : Set where
  constructor c[_,_]
  field name : String
        type : Type

record Variable : Set where
  constructor v[_,_]
  field name : String
        type : Type

data Term : {_ : Type} -> Set where
  Var   : (v : Variable) -> Term {Variable.type v}
  Const : (c : Constant) -> Term {Constant.type c}
  App   : ∀ {x} {y} -> Term {x => y} -> Term {x} -> Term {y}
  Abs   : ∀ {y} -> (v : Variable) -> Term {y} -> Term {(Variable.type v) => y}

open import Relation.Binary using (Rel)
open import Relation.Binary.Product.StrictLex using (×-Lex)
open import Data.Product using (_,_)
open import Relation.Binary.Core using (_≡_)
open import Function using (_on_)

infix 4 _var<_
_var<_ : Rel Variable _
_var<_ = ×-Lex _≡_ _S<_  _ty<_ on (λ v → Variable.name v , Variable.type v)

-- infix 4 _<_
-- data _<_ : Rel Term _ where
--   Var<Var :

Formula : Set
Formula = Term {bool}

-- strict total order on terms?
-- alpha equivalence?

equality : Constant
equality = record { name = fromString "="; type = α => α => bool }

-- substitutions
-- inst_type
-- (inst)

-- data Thm : ⟨Set⟩ Formula -> Formula where
--  Assume : ∀ t -> Thm (singleton t) t
