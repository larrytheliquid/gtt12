open import Prelude
open import Equivalences
open import Monoids
open import Data.Nat
module EquivalenceMonoids where

----------------------------------------------------------------------

record Monoid/≈ (S : Set) (_≈_ : S → S → Set) : Set₁ where
  infixr 9 _∙_
  field
    eq : Equivalence _≈_
    ı : S
    _∙_ : (x y : S) → S

    identl : (x : S) → (ı ∙ x) ≈ x
    identr : (x : S) → (x ∙ ı) ≈ x
    assoc : (x y z : S) →
      (x ∙ (y ∙ z)) ≈ ((x ∙ y) ∙ z)

----------------------------------------------------------------------

Monoidℕ/≡ : Monoid/≈ ℕ _≡_
Monoidℕ/≡ = record
  { eq = Equivalence≡
  ; ı = Monoid.ı Monoidℕ
  ; identl = Monoid.identl Monoidℕ
  ; identr = Monoid.identr Monoidℕ
  ; assoc = Monoid.assoc Monoidℕ
  }

----------------------------------------------------------------------
