open import Name using (Name)

module Hol.Type (Names : Name) where

open import Data.Nat using (ℕ) renaming (_<_ to _N<_)
open import Data.Nat.Properties using () renaming (<-trans to N<-trans)
open import Data.Vec using (Vec;_∷_;[_];[]) renaming (toList to Vec→List)
open import Data.Product using (_,_;Σ)
open import Function using (_on_)
open import Relation.Binary using (Rel;StrictTotalOrder;IsStrictTotalOrder;Transitive;Trichotomous;tri<;tri≈;tri>)
open import Relation.Binary.Product.StrictLex using (×-Lex;×-transitive;×-compare)
open import Relation.Binary.List.StrictLex using (Lex-<) renaming (transitive to Lex<-trans)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
import Relation.Binary.On as On
open import Relation.Nullary using (¬_)

String = Name.Carrier Names
fromString = Name.fromString Names
_S<_ = Name._<_ Names
S<-trans : Transitive _S<_
S<-trans = Name.trans Names
S<-cmp   = Name.compare Names
N<-cmp   = StrictTotalOrder.compare (Data.Nat.Properties.strictTotalOrder)

record TypeOperator : Set where
  field name  : String
        arity : ℕ

data Type : Set where
  TyVar : String → Type
  TyApp : (op : TypeOperator) → Vec Type (TypeOperator.arity op) → Type

op→pair : TypeOperator →  Σ String (λ _ → ℕ)
op→pair op = TypeOperator.name op , TypeOperator.arity op

infix 4 _op<_
_op<_ : Rel TypeOperator _
_op<_ = ×-Lex _≡_ _S<_ _N<_ on op→pair

op<-trans : Transitive _op<_
op<-trans = On.transitive (λ op → TypeOperator.name op , TypeOperator.arity op) (×-Lex _≡_ _S<_ _N<_) (×-transitive PropEq.isEquivalence (PropEq.resp₂ _S<_) S<-trans {_≤₂_ = _N<_} N<-trans)

op<-cmp : Trichotomous {- want this to be _≡_ -} _ _op<_
op<-cmp = On.trichotomous op→pair _ (×-Lex _≡_ _S<_ _N<_ ) (×-compare PropEq.sym S<-cmp N<-cmp)

infix 4 _<_
data _<_ : Rel Type _ where
  TyVar<TyVar : ∀ {s₁} {s₂} → (s₁<s₂ : s₁ S< s₂) → TyVar s₁ < TyVar s₂
  TyVar<TyApp : ∀ {s} {op} {as} → TyVar s < TyApp op as
  TyApp<TyApp : ∀ {op₁} {as₁} {op₂} {as₂} → ×-Lex _≡_ _op<_ (Lex-< _≡_ _<_) (op₁ , Vec→List as₁) (op₂ , Vec→List as₂) → TyApp op₁ as₁ < TyApp op₂ as₂

_app<_ = ×-Lex _≡_ _op<_ (Lex-< _≡_ _<_)
app<-cmp : Trichotomous _ _app<_
app<-cmp = ×-compare {!!} {!op<-cmp!} {!!}

<-trans : Transitive _<_
<-trans (TyVar<TyVar p) (TyVar<TyVar q) = TyVar<TyVar (S<-trans p q)
<-trans (TyVar<TyVar _) TyVar<TyApp = TyVar<TyApp
<-trans TyVar<TyApp (TyApp<TyApp _) = TyVar<TyApp
<-trans (TyApp<TyApp p) (TyApp<TyApp q) = TyApp<TyApp (×-transitive PropEq.isEquivalence (PropEq.resp₂ _op<_) op<-trans {_≤₂_ = Lex-< _≡_ _<_ } (Lex<-trans PropEq.isEquivalence (PropEq.resp₂ _<_) <-trans) p q)

TyVar-inj : ∀ {x y} → ¬ (x ≡ y) → ¬ (TyVar x ≡ TyVar y)
TyVar-inj {x} {.x} ne PropEq.refl = ne PropEq.refl

TyVar-S< : ∀ {x y} → ¬ (x S< y) → ¬ (TyVar x < TyVar y)
TyVar-S< gt (TyVar<TyVar s₁<s₂) = gt s₁<s₂

<-cmp : Trichotomous _≡_ _<_
<-cmp (TyVar s₁) (TyVar s₂) with S<-cmp s₁ s₂
... | tri< a ¬b ¬c = tri< (TyVar<TyVar a) (TyVar-inj        ¬b) (TyVar-S<   ¬c)
... | tri≈ ¬a b ¬c = tri≈ (TyVar-S<   ¬a) (PropEq.cong TyVar b) (TyVar-S<   ¬c)
... | tri> ¬a ¬b c = tri> (TyVar-S<   ¬a) (TyVar-inj        ¬b) (TyVar<TyVar c)
<-cmp (TyVar _) (TyApp _ _) = tri< TyVar<TyApp (λ ()) (λ ())
<-cmp (TyApp _ _) (TyVar _) = tri> (λ ()) (λ ()) TyVar<TyApp
<-cmp (TyApp op₁ as₁) (TyApp op₂ as₂) = {!!}

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
fun_tyop = record { name = fromString "->"; arity = 2 }
infixr 30 _=>_
_=>_     : Type -> Type -> Type
t₁ => t₂ = TyApp fun_tyop (t₁ ∷ [ t₂ ])

bool_tyop : TypeOperator
bool_tyop = record { name = fromString "bool"; arity = 0 }
bool : Type
bool = TyApp bool_tyop []

α : Type
α = TyVar (fromString "A")
