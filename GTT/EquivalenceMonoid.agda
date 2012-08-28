open import GTT.Equality
open import GTT.Equivalence
open import GTT.Monoid
open import Data.Nat
module GTT.EquivalenceMonoid where

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
  ; _∙_ = Monoid._∙_ Monoidℕ
  ; identl = Monoid.identl Monoidℕ
  ; identr = Monoid.identr Monoidℕ
  ; assoc = Monoid.assoc Monoidℕ
  }

----------------------------------------------------------------------

Monoidλ/≣ : {A : Set} → Monoid/≈ (A → A) _≣_
Monoidλ/≣ = record
  { eq = Equivalence≣
  ; ı = id
  ; _∙_ = _∘_
  ; identl = λ _ _ → refl
  ; identr = λ _ _ → refl
  ; assoc = λ _ _ _ _ → refl
  }

----------------------------------------------------------------------