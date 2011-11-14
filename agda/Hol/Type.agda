module Hol.Type where

open import Data.String using (String)
open import Data.Nat using (ℕ) renaming (_<_ to _N<_)
open import Data.Vec using (Vec;_∷_;[_];[])

record TypeOperator : Set where
  field name  : String
        arity : ℕ

data Type : Set where
  TyVar : String → Type
  TyApp : (op : TypeOperator) → Vec Type (TypeOperator.arity op) → Type

open import Relation.Binary using (Rel)
open import Relation.Binary.List.StrictLex using (Lex-<)
open import Data.Char using ()
open import Relation.Binary.Core using (_≡_)

infix 4 _str<_
_str<_ : Rel String _
s₁ str< s₂ = Lex-< _≡_ (λ c₁ c₂ → Data.Char.toNat c₁ N< Data.Char.toNat c₂) (Data.String.toList s₁) (Data.String.toList s₂)

open import Relation.Binary.Product.StrictLex using (×-Lex)
open import Data.Product using (_,_)

infix 4 _op<_
_op<_ : Rel TypeOperator _
op₁ op< op₂ = ×-Lex _≡_ _str<_ _N<_ (TypeOperator.name op₁ , TypeOperator.arity op₁) (TypeOperator.name op₂ , TypeOperator.arity op₂)

open import Level using ()

infix 4 _<_
data _<_ : Rel Type Level.zero where
  TyVar<TyVar : ∀ {s₁} {s₂} → (s₁<s₂ : s₁ str< s₂) → TyVar s₁ < TyVar s₂
  TyVar<TyApp : ∀ {s} {op} {args} → TyVar s < TyApp op args
--  TyApp<TyApp : ∀ {op₁} {args₁} {op₂} {args₂} → → TyApp op₁ args₁ < TyApp op₂ args₂

fun_tyop : TypeOperator
fun_tyop = record { name = "->"; arity = 2 }
infixr 30 _⇒_
_⇒_     : Type -> Type -> Type
t₁ ⇒ t₂ = TyApp fun_tyop (t₁ ∷ [ t₂ ])

bool_tyop : TypeOperator
bool_tyop = record { name = "bool"; arity = 0 }
bool : Type
bool = TyApp bool_tyop []
