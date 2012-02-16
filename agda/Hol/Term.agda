{-# OPTIONS --sized-types #-}
open import Name using (Name)
module Hol.Term (Names : Name) where

import Hol.Type
open Hol.Type (Names) using (Type;α;_=>_;bool) renaming (_<_ to _ty<_)
open import Size using (Size;↑_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (_×_;_,_)

String = Name.Carrier Names
_S<_ = Name._<_ Names
fromString = Name.fromString Names

record Constant : Set where
  constructor c[_,_]
  field
    name : String
    {size} : Size
    type : Type {↑ size}

record Variable : Set where
  constructor v[_,_]
  field
    name : String
    {size} : Size
    type : Type {↑ size}

Variable→pair : ∀ {z} → (v : Variable) → Variable.size v ≡ z → String × Type {z}
Variable→pair v[ n , ty ] p = n , {!ty!}

data Term : {z : Size} → {_ : Type {z}} → Set where
  Var   : ∀ {z} → (v : Variable) → Variable.size v ≡ z → Term {↑ z} { {!!} } -- {Variable.type v}
  Const : ∀ {z} → (c[ _ , ty ] : Constant) → Term {↑ z} { {!!} }
--  App   : ∀ {z} {x} {y} → Term {z} {x => y} → Term {z} {x} → Term {↑ z} {y}
--  Abs   : ∀ {z} {y} → (v[ _ , ty ] : Variable) → Term {z} {y} → Term {↑ z} {ty => y}

open import Relation.Binary using (Rel)
open import Relation.Binary.Product.StrictLex using (×-Lex)
open import Data.Product using (_,_)
open import Relation.Binary.Core using (_≡_)
open import Function using (_on_)

infix 4 _var<_
_var<_ : Rel Variable _
_var<_ = ×-Lex _≡_ _S<_  _ty<_ on Variable→pair

-- infix 4 _<_
-- data _<_ : Rel Term _ where
--   Var<Var :

-- Formula : Set
-- Formula = Term {bool}

-- strict total order on terms?
-- alpha equivalence?

equality : Constant
equality = record { name = fromString "="; type = α => α => bool }

-- substitutions
-- inst_type
-- (inst)

-- data Thm : ⟨Set⟩ Formula -> Formula where
--  Assume : ∀ t -> Thm (singleton t) t
