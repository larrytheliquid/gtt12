open import Prelude
module Categories where

record Category : Set₁ where
  infixr 9 _∙_
  field
    S : Set
    _➛_ : (A B : S) → Set

    ı : {A : S} → A ➛ A
    _∙_ : {A B C : S}
      (x : A ➛ B) (y : B ➛ C) → A ➛ C

    identl : {A B : S} (x : A ➛ B) →
      x ∙ ı ≡ x
    identr : {A B : S} (x : A ➛ B) →
      ı ∙ x ≡ x
    assoc : {A B C D : S}
      (x : A ➛ B) (y : B ➛ C) (z : C ➛ D) →
      (x ∙ (y ∙ z)) ≡ ((x ∙ y) ∙ z)

