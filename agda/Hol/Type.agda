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
open import Function using (_on_)

infix 4 _str<_
_str<_ : Rel String _
_str<_ = Lex-< _≡_ (_N<_ on Data.Char.toNat) on (Data.String.toList)

open import Relation.Binary.Product.StrictLex using (×-Lex)
open import Data.Product using (_,_)

infix 4 _op<_
_op<_ : Rel TypeOperator _
_op<_ = ×-Lex _≡_ _str<_ _N<_ on (λ op -> TypeOperator.name op , TypeOperator.arity op)

infix 4 _<_
data _<_ : Rel Type _ where
  TyVar<TyVar : ∀ {s₁} {s₂} → (s₁<s₂ : s₁ str< s₂) → TyVar s₁ < TyVar s₂
  TyVar<TyApp : ∀ {s} {op} {as} → TyVar s < TyApp op as
  TyApp<TyApp : ∀ {op₁} {as₁} {op₂} {as₂} → ×-Lex _≡_ _op<_ (Lex-< _≡_ _<_) (op₁ , Data.Vec.toList as₁) (op₂ , Data.Vec.toList as₂) → TyApp op₁ as₁ < TyApp op₂ as₂

fun_tyop : TypeOperator
fun_tyop = record { name = "->"; arity = 2 }
infixr 30 _⇒_
_⇒_     : Type -> Type -> Type
t₁ ⇒ t₂ = TyApp fun_tyop (t₁ ∷ [ t₂ ])

bool_tyop : TypeOperator
bool_tyop = record { name = "bool"; arity = 0 }
bool : Type
bool = TyApp bool_tyop []
