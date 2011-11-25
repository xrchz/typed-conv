module Name where

open import Relation.Binary using (module IsStrictTotalOrder; IsStrictTotalOrder; Rel)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.String using (String)
open import Level using (zero)

record Name : Set₁ where
  field
    Carrier : Set
    _<_     : Rel Carrier zero
    isStrictTotalOrder : IsStrictTotalOrder _≡_ _<_
    fromString : String → Carrier
    
  open IsStrictTotalOrder isStrictTotalOrder public