module Hol.Type where

open import Data.String using (String) renaming (strictTotalOrder to StringSTO)
open import Data.Nat using (ℕ) renaming (_<_ to _N<_)
open import Data.Nat.Properties using () renaming (<-trans to N<-trans)
open import Data.Vec using (Vec;_∷_;[_];[]) renaming (toList to Vec→List)
open import Data.Product using (_,_)
open import Function using (_on_)
open import Relation.Binary using (Rel;IsStrictTotalOrder;StrictTotalOrder;Transitive;Trichotomous;tri<;tri≈;tri>)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
open import Relation.Binary.Product.StrictLex using (×-Lex;×-transitive)
open import Relation.Binary.List.StrictLex using (Lex-<) renaming (transitive to Lex<-trans)
import Relation.Binary.On as On
open import Relation.Nullary using (¬_)

_S<_ = StrictTotalOrder._<_ StringSTO
S<-trans : Transitive _S<_
S<-trans {i} {j} {k} = StrictTotalOrder.trans StringSTO {i} {j} {k}
S<-cmp : Trichotomous _ _S<_
S<-cmp = StrictTotalOrder.compare StringSTO

record TypeOperator : Set where
  field name  : String
        arity : ℕ

data Type : Set where
  TyVar : String → Type
  TyApp : (op : TypeOperator) → Vec Type (TypeOperator.arity op) → Type

infix 4 _op<_
_op<_ : Rel TypeOperator _
_op<_ = ×-Lex _≡_ _S<_ _N<_ on (λ op → TypeOperator.name op , TypeOperator.arity op)

op<-trans : Transitive _op<_
op<-trans = On.transitive (λ op → TypeOperator.name op , TypeOperator.arity op) (×-Lex _≡_ _S<_ _N<_) (×-transitive PropEq.isEquivalence (PropEq.resp₂ _S<_) (λ {i} {j} {k} → S<-trans {i} {j} {k}) {_≤₂_ = _N<_} N<-trans)

infix 4 _<_
data _<_ : Rel Type _ where
  TyVar<TyVar : ∀ {s₁} {s₂} → (s₁<s₂ : s₁ S< s₂) → TyVar s₁ < TyVar s₂
  TyVar<TyApp : ∀ {s} {op} {as} → TyVar s < TyApp op as
  TyApp<TyApp : ∀ {op₁} {as₁} {op₂} {as₂} → ×-Lex _≡_ _op<_ (Lex-< _≡_ _<_) (op₁ , Vec→List as₁) (op₂ , Vec→List as₂) → TyApp op₁ as₁ < TyApp op₂ as₂

<-trans : Transitive _<_
<-trans (TyVar<TyVar {i} {j} p) (TyVar<TyVar {s₂ = k} q) = TyVar<TyVar (S<-trans {i} {j} {k} p q)
<-trans (TyVar<TyVar _) TyVar<TyApp = TyVar<TyApp
<-trans TyVar<TyApp (TyApp<TyApp _) = TyVar<TyApp
<-trans (TyApp<TyApp p) (TyApp<TyApp q) = TyApp<TyApp (×-transitive PropEq.isEquivalence (PropEq.resp₂ _op<_) op<-trans {_≤₂_ = Lex-< _≡_ _<_ } (Lex<-trans PropEq.isEquivalence (PropEq.resp₂ _<_) <-trans) p q)

TyVar-inj : ∀ x y → ¬ (x ≡ y) → ¬ (TyVar x ≡ TyVar y)
TyVar-inj x .x ne PropEq.refl = ne PropEq.refl

<-cmp : Trichotomous _≡_ _<_
<-cmp (TyVar s₁) (TyVar s₂) with S<-cmp s₁ s₂
... | tri< a ¬b ¬c = tri< (TyVar<TyVar a) (TyVar-inj s₁ s₂ {!¬b!}) {!!}
... | tri≈ ¬a b ¬c = {!!}
... | tri> ¬a ¬b c = {!!}
<-cmp (TyVar _) (TyApp _ _) = tri< TyVar<TyApp (λ ()) {!!}
<-cmp (TyApp _ _) (TyVar _) = {!!}
<-cmp (TyApp _ _) (TyApp _ _) = {!!}

strictTotalOrder : StrictTotalOrder _ _ _
strictTotalOrder = record
  { _<_ = _<_
  ; isStrictTotalOrder = record
      { isEquivalence = PropEq.isEquivalence
      ; trans         = <-trans
      ; compare       = <-cmp
      ; <-resp-≈      = PropEq.resp₂ _<_
      }
  }

fun_tyop : TypeOperator
fun_tyop = record { name = "->"; arity = 2 }
infixr 30 _=>_
_=>_     : Type -> Type -> Type
t₁ => t₂ = TyApp fun_tyop (t₁ ∷ [ t₂ ])

bool_tyop : TypeOperator
bool_tyop = record { name = "bool"; arity = 0 }
bool : Type
bool = TyApp bool_tyop []

α : Type
α = TyVar "A"
