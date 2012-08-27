open import Prelude hiding ( id ; _∘_ )
module Categories where

record Category : Set₁ where
  infixr 9 _∙_
  field
    S : Set
    _➛_ : (A B : S) → Set

    e : {A : S} → A ➛ A
    _∙_ : {A B C : S}
      (x : A ➛ B) (y : B ➛ C) → A ➛ C

    identl : {A B : S} (x : A ➛ B) →
      x ∙ e ≡ x
    identr : {A B : S} (x : A ➛ B) →
      e ∙ x ≡ x
    assoc : {A B C D : S}
      (x : A ➛ B) (y : B ➛ C) (z : C ➛ D) →
      (x ∙ (y ∙ z)) ≡ ((x ∙ y) ∙ z)