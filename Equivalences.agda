open import Prelude
open import Isomorphisms
module Equivalences where

record Equivalence {A : Set} (_≈_ : A → A → Set) : Set where
  field
    refl≈ : {x : A} → x ≈ x
    sym≈ : {x y : A} → x ≈ y → y ≈ x
    trans≈ : {x y z : A} → x ≈ y → y ≈ z → x ≈ z

Equivalence≡ : {A : Set} → Equivalence {A} _≡_
Equivalence≡ = record
  { refl≈  = refl
  ; sym≈   = sym
  ; trans≈ = trans
  }

