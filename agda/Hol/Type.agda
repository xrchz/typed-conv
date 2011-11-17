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

open import Relation.Binary using (Rel;IsStrictTotalOrder;StrictTotalOrder;Transitive)
open import Relation.Binary.List.StrictLex as ListLex using (Lex-<)
import Data.Char
open import Relation.Binary.Core using (_≡_)
open import Function using (_on_;_∘_)

import Data.List
import Relation.Binary.List.Pointwise as Pointwise
import Relation.Binary.PropositionalEquality as PropEq
open import Data.Nat.Properties renaming (<-trans to N<-trans; strictTotalOrder to Nsto)
import Level

infix 4 _ListChar<_
_ListChar<_ : Rel (Data.List.List Data.Char.Char) _
_ListChar<_ = Lex-< _≡_ (_N<_ on Data.Char.toNat)

ListChar<-isStrictTotalOrder : IsStrictTotalOrder (Pointwise.Rel _≡_) _ListChar<_
ListChar<-isStrictTotalOrder = ListLex.<-isStrictTotalOrder record
  { isEquivalence = PropEq.isEquivalence
  ; trans = N<-trans
  ; compare = {!(IsStrictTotalOrder.compare (StrictTotalOrder.isStrictTotalOrder Nsto)) on Data.Char.toNat!}
  ; <-resp-≈ = {!!}
  }

infix 4 _str<_
_str<_ : Rel String _
_str<_ = _ListChar<_ on (Data.String.toList)

open import Relation.Binary using (IsEquivalence)

IsEquivalence-on : ∀ {a b l} {A : Set a} {B : Set b} {_≈_ : Rel A l} {f : B → A} → IsEquivalence _≈_ → IsEquivalence (_≈_ on f)
IsEquivalence-on e = record { refl = IsEquivalence.refl e ; sym = IsEquivalence.sym e ; trans = IsEquivalence.trans e }

IsStrictTotalOrder-on : ∀ {a b l₁ l₂} {A : Set a} {B : Set b} {_≈_ : Rel A l₁} {_<_ : Rel A l₂} {f : B → A} → IsStrictTotalOrder _≈_ _<_ → IsStrictTotalOrder (_≈_ on f) (_<_ on f)
IsStrictTotalOrder-on {_<_ = _<_} {f = f} sto = record
  { isEquivalence = IsEquivalence-on (IsStrictTotalOrder.isEquivalence sto)
  ; trans = IsStrictTotalOrder.trans sto
  ; compare = {!!}
  ; <-resp-≈ = {!!}
  }

str<-isStrictTotalOrder : IsStrictTotalOrder (_≡_ on Data.String.toList) _str<_
str<-isStrictTotalOrder = IsStrictTotalOrder-on {!!} -- (ListLex.<-isStrictTotalOrder ?)

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

isTransitive : Transitive _<_
isTransitive (TyVar<TyVar s₁<s₂) (TyVar<TyVar s₂<s₃) = {!!}
isTransitive _ _ = {!!}

isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
isStrictTotalOrder = record {
  isEquivalence = PropEq.isEquivalence;
  trans = {!!};
  compare = {!!};
  <-resp-≈ = {!!} }

fun_tyop : TypeOperator
fun_tyop = record { name = "->"; arity = 2 }
infixr 30 _⇒_
_⇒_     : Type -> Type -> Type
t₁ ⇒ t₂ = TyApp fun_tyop (t₁ ∷ [ t₂ ])

bool_tyop : TypeOperator
bool_tyop = record { name = "bool"; arity = 0 }
bool : Type
bool = TyApp bool_tyop []

α : Type
α = TyVar "A"
