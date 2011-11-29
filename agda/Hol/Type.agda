open import Name using (Name)

module Hol.Type (Names : Name) where

open import Data.Nat using (ℕ) renaming (_<_ to _N<_)
open import Data.Nat.Properties using () renaming (<-trans to N<-trans)
open import Data.Vec using (Vec;_∷_;[_];[]) renaming (toList to Vec→List;fromList to List→Vec)
open import Data.Product using (_,_;_×_)
import Data.List
open import Data.List.Properties using (∷-injective)
open import Data.Sum using (inj₁)
open import Function using (_on_)
open import Function.Injection using (Injective)
open import Function.Equality using (Π;_⟶_)
open import Function.Inverse using (Inverse)
open import Relation.Binary using (Rel;StrictTotalOrder;IsStrictTotalOrder;Transitive;Trichotomous;tri<;tri≈;tri>;_⇒_)
open import Relation.Binary.Product.StrictLex using (×-Lex;×-transitive;×-compare)
open import Relation.Binary.Product.Pointwise using (_×-Rel_;×-Rel↔≡)
open import Relation.Binary.List.StrictLex using (Lex-<;<-compare) renaming (transitive to Lex<-trans)
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_)
import Relation.Binary.On as On
import Relation.Binary.List.Pointwise as Pointwise
open import Relation.Nullary using (¬_)
open import Level using (_⊔_)

String = Name.Carrier Names
fromString = Name.fromString Names
_S<_ = Name._<_ Names
S<-trans : Transitive _S<_
S<-trans = Name.trans Names
S<-cmp   = Name.compare Names
N<-cmp   = StrictTotalOrder.compare (Data.Nat.Properties.strictTotalOrder)

record TypeOperator : Set where
  constructor op[_,_]
  field name  : String
        arity : ℕ

data Type : Set where
  TyVar : String → Type
  TyApp : (op : TypeOperator) → Vec Type (TypeOperator.arity op) → Type

op→pair : TypeOperator →  String × ℕ
op→pair op[ name , arity ] = name , arity

infix 4 _op<_
_op<_ : Rel TypeOperator _
_op<_ = ×-Lex _≡_ _S<_ _N<_ on op→pair

op<-trans : Transitive _op<_
op<-trans = On.transitive (λ op → TypeOperator.name op , TypeOperator.arity op) (×-Lex _≡_ _S<_ _N<_) (×-transitive PropEq.isEquivalence (PropEq.resp₂ _S<_) S<-trans {_≤₂_ = _N<_} N<-trans)

{---8<--- from Saizan, hpaste.org/54659 -}
to≡ : ∀ {l₁ l₂} {A : Set l₁}{B : Set l₂} {x y : A × B} -> (_≡_ ×-Rel _≡_) x y -> x ≡ y
to≡ {x = .c , .d} {y = c , d} (PropEq.refl , PropEq.refl) = PropEq.refl

from≡ : ∀ {l₁ l₂} {A : Set l₁}{B : Set l₂} {x y : A × B} -> x ≡ y -> (_≡_ ×-Rel _≡_) x y
from≡ PropEq.refl = PropEq.refl , PropEq.refl

foo : ∀ {l₁ l₂} {A : Set l₁} {B : Set l₂} {_<_ : Rel (A × B) (l₁ ⊔ l₂)} → Trichotomous (_≡_ ×-Rel _≡_) _<_ → Trichotomous _≡_ _<_
foo t x y with t x y
foo t x y | tri< a ¬b ¬c = tri< a (λ p → ¬b (from≡ p)) ¬c
foo t x y | tri≈ ¬a b ¬c = tri≈ ¬a (to≡ b) ¬c
foo t x y | tri> ¬a ¬b c = tri> ¬a (λ p → ¬b (from≡ p)) c
{---8<---}

opp<-cmp : Trichotomous _≡_ (×-Lex _≡_ _S<_ _N<_)
opp<-cmp = foo (×-compare PropEq.sym S<-cmp N<-cmp)

-- Injection→Function : ∀ {a b} {A : Set a} {B : Set b} → A ↣ B → (A → B)
-- Injection→Function i = Π._⟨$⟩_ (Injection.to i)

foo2 : ∀ {m n} {A : Set m} {B : Set n} {f : B → A} {_<_ : Rel B n} → Injective (PropEq.→-to-⟶ {B = PropEq.setoid A} f) → Trichotomous (_≡_ on f) _<_ → Trichotomous _≡_ _<_
foo2 i t x y with t x y
... | tri< a ¬b ¬c = tri< a (λ p → ¬b (PropEq.cong _ p)) ¬c
... | tri≈ ¬a b ¬c = tri≈ ¬a (i b) ¬c
... | tri> ¬a ¬b c = tri> ¬a (λ p → ¬b (PropEq.cong _ p)) c

op→pair-Injective : Injective (PropEq.→-to-⟶ {B = PropEq.setoid _} op→pair)
op→pair-Injective {op[ _ , _ ]} {op[ ._ , ._ ]} PropEq.refl = PropEq.refl

op<-cmp : Trichotomous _≡_ _op<_
op<-cmp = foo2 op→pair-Injective (On.trichotomous op→pair _ (×-Lex _≡_ _S<_ _N<_ ) opp<-cmp)

infix 4 _<_
data _<_ : Rel Type _ where
  TyVar<TyVar : ∀ {s₁} {s₂} → (s₁<s₂ : s₁ S< s₂) → TyVar s₁ < TyVar s₂
  TyVar<TyApp : ∀ {s} {op} {as} → TyVar s < TyApp op as
  TyApp<TyApp : ∀ {op₁} {as₁} {op₂} {as₂} → ×-Lex _≡_ _op<_ (Lex-< _≡_ _<_) (op₁ , Vec→List as₁) (op₂ , Vec→List as₂) → TyApp op₁ as₁ < TyApp op₂ as₂

foo3 : ∀ {a} {A : Set a} {_<_ : Rel (Data.List.List A) a} → Trichotomous (Pointwise.Rel _≡_) _<_ → Trichotomous _≡_ _<_
foo3 t x y with t x y
foo3 t x y | tri< a ¬b ¬c = tri< a (λ p → ¬b (Pointwise.≡⇒Rel≡ p)) ¬c
foo3 t x y | tri≈ ¬a b ¬c = tri≈ ¬a (Pointwise.Rel≡⇒≡ b) ¬c
foo3 t x y | tri> ¬a ¬b c = tri> ¬a (λ p → ¬b (Pointwise.≡⇒Rel≡ p)) c

TyVar-inj : ∀ {x y} → ¬ (x ≡ y) → ¬ (TyVar x ≡ TyVar y)
TyVar-inj ne PropEq.refl = ne PropEq.refl

TyVar-S< : ∀ {x y} → ¬ (x S< y) → ¬ (TyVar x < TyVar y)
TyVar-S< gt (TyVar<TyVar s₁<s₂) = gt s₁<s₂

-- TyApp-op-inj : ∀ {op₁ op₂ as₁ as₂} → ¬ (op₁ ≡ op₂) → ¬ (TyApp op₁ as₁ ≡ TyApp op₂ as₂)
-- TyApp-op-inj ne PropEq.refl = ne PropEq.refl

TyApp-inj : ∀ {op₁ op₂ as₁ as₂} → ¬ (op₁ , Vec→List as₁ ≡ op₂ , Vec→List as₂) → ¬ (TyApp op₁ as₁ ≡ TyApp op₂ as₂)
TyApp-inj ne PropEq.refl = ne PropEq.refl

Vec→List-inj : ∀ {l} {A : Set l} {n} {v w : Vec A n} → Vec→List v ≡ Vec→List w → v ≡ w
Vec→List-inj {l} {A} {Data.Nat.zero} {[]} {[]} eq = PropEq.refl
Vec→List-inj {l} {A} {Data.Nat.suc n} {x ∷ xs} {y ∷ ys} eq with ∷-injective eq
Vec→List-inj {l} {A} {Data.Nat.suc n} {x ∷ xs} {y ∷ ys} eq | x≡y , xs≡ys = PropEq.cong₂ _∷_ x≡y (Vec→List-inj xs≡ys)

TyApp-inj' : ∀ {op₁ op₂ as₁ as₂} → (op₁ , Vec→List as₁ ≡ op₂ , Vec→List as₂) → (TyApp op₁ as₁ ≡ TyApp op₂ as₂)
TyApp-inj' eq with PropEq.cong Data.Product.proj₁ eq
TyApp-inj' eq | PropEq.refl with PropEq.cong Data.Product.proj₂ eq
TyApp-inj' eq | PropEq.refl | z with Vec→List-inj z
TyApp-inj' eq | PropEq.refl | _ | PropEq.refl = PropEq.refl

TyApp-< : ∀ {op₁ op₂ as₁ as₂} → ¬ (×-Lex _≡_ _op<_ (Lex-< _≡_ _<_) (op₁ , Vec→List as₁) (op₂ , Vec→List as₂)) → ¬ (TyApp op₁ as₁ < TyApp op₂ as₂)
TyApp-< gt (TyApp<TyApp p) = gt p

_app<_ = ×-Lex _≡_ _op<_ (Lex-< _≡_ _<_)

mutual
  app<-cmp : Trichotomous _≡_ _app<_
  app<-cmp = foo (×-compare PropEq.sym op<-cmp (foo3 (<-compare PropEq.sym <-cmp)))

  <-cmp : Trichotomous _≡_ _<_
  <-cmp (TyVar s₁) (TyVar s₂) with S<-cmp s₁ s₂
  ... | tri< a ¬b ¬c = tri< (TyVar<TyVar a) (TyVar-inj        ¬b) (TyVar-S<   ¬c)
  ... | tri≈ ¬a b ¬c = tri≈ (TyVar-S<   ¬a) (PropEq.cong TyVar b) (TyVar-S<   ¬c)
  ... | tri> ¬a ¬b c = tri> (TyVar-S<   ¬a) (TyVar-inj        ¬b) (TyVar<TyVar c)
  <-cmp (TyVar _) (TyApp _ _) = tri< TyVar<TyApp (λ ()) (λ ())
  <-cmp (TyApp _ _) (TyVar _) = tri> (λ ()) (λ ()) TyVar<TyApp
  <-cmp (TyApp op₁ as₁) (TyApp op₂ as₂) with app<-cmp (op₁ , Vec→List as₁) (op₂ , Vec→List as₂)
  ... | tri< a ¬b ¬c = tri< (TyApp<TyApp a) (TyApp-inj ¬b) (TyApp-< ¬c)
  ... | tri≈ ¬a b ¬c = tri≈ (TyApp-< ¬a) (TyApp-inj' b) (TyApp-< ¬c)
  ... | tri> ¬a ¬b c = tri> (TyApp-< ¬a) (TyApp-inj ¬b) (TyApp<TyApp c)

  {-
  <-cmp (TyApp op₁ as₁) (TyApp op₂ as₂) | tri< a ¬b ¬c = tri< (TyApp<TyApp (inj₁ a)) (TyApp-op-inj ¬b) (λ p → ¬c {!p!})
  <-cmp (TyApp op₁ as₁) (TyApp op₂ as₂) | tri≈ ¬a b ¬c with as<-cmp (Vec→List as₁) (Vec→List as₂)
  <-cmp (TyApp op₁ as₁) (TyApp op₂ as₂) | tri≈ ¬a b ¬c' | tri< a ¬b ¬c = tri< {!!} {!!} {!!}
  <-cmp (TyApp op₁ as₁) (TyApp op₂ as₂) | tri≈ ¬a' b' ¬c' | tri≈ ¬a b ¬c = tri≈ {!!} {!!} {!!}
  <-cmp (TyApp op₁ as₁) (TyApp op₂ as₂) | tri≈ ¬a' b ¬c | tri> ¬a ¬b c = tri> {!!} {!!} {!!}
  <-cmp (TyApp op₁ as₁) (TyApp op₂ as₂) | tri> ¬a ¬b c = tri> {!!} (TyApp-op-inj ¬b) (TyApp<TyApp (inj₁ c))
  -}

<-trans : Transitive _<_
<-trans (TyVar<TyVar p) (TyVar<TyVar q) = TyVar<TyVar (S<-trans p q)
<-trans (TyVar<TyVar _) TyVar<TyApp = TyVar<TyApp
<-trans TyVar<TyApp (TyApp<TyApp _) = TyVar<TyApp
<-trans (TyApp<TyApp p) (TyApp<TyApp q) = TyApp<TyApp (×-transitive PropEq.isEquivalence (PropEq.resp₂ _op<_) op<-trans {_≤₂_ = Lex-< _≡_ _<_ } (Lex<-trans PropEq.isEquivalence (PropEq.resp₂ _<_) <-trans) p q)

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
