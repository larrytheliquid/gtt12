open import Prelude
module Categories where

record Category (S : Set) : Set₁ where
  infixr 9 _∙_
  field
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

record Functor {S S′} (∁ : Category S) (∁′ : Category S′) : Set where
  open Category ∁
  open Category ∁′ renaming ( _➛_ to _➛′_ ; ı to ı′ ; _∙_ to _∙′_ )
  field
    ∣f∣ : (X : S) → S′
    f : {X Y : S} (f : X ➛ Y) → ∣f∣ X ➛′ ∣f∣ Y
    preserves-ı : {X : S} →
      f {X} ı ≡ ı′
    preserves-∙ : {X Y Z : S}
      (x : X ➛ Y) (y : Y ➛ Z) →
      f (x ∙ y) ≡ f x ∙′ f y

record NaturalTransformation {S S′} {∁ : Category S} {∁′ : Category S′}
  (F G : Functor ∁ ∁′) : Set where
  open Functor F
  open Functor G renaming ( ∣f∣ to ∣f∣′ ; f to f′ )
  open Category ∁
  open Category ∁′ renaming
    ( _➛_ to _➛′_ ; ı to ı′ ; _∙_ to _∙′_ )

  field
    g : {A : S} → ∣f∣ A ➛′ ∣f∣′ A
    natural : {A B : S} (x : A ➛ B) →
      g ∙′ f′ x ≡ f x ∙′ g