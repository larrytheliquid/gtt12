open import Prelude
module Equivalences where

infix 4 _≣_

----------------------------------------------------------------------

record Equivalence {A : Set} (_≈_ : A → A → Set) : Set where
  field
    refl≈ : {x : A} → x ≈ x
    sym≈ : {x y : A} → x ≈ y → y ≈ x
    trans≈ : {x y z : A} → x ≈ y → y ≈ z → x ≈ z

----------------------------------------------------------------------

Equivalence≡ : {A : Set} → Equivalence {A} _≡_
Equivalence≡ = record
  { refl≈  = refl
  ; sym≈   = sym
  ; trans≈ = trans
  }

----------------------------------------------------------------------

_≣_ : {A B : Set} (f g : A → B) → Set
f ≣ g = ∀ a → f a ≡ g a

refl≣ : {A B : Set} {f : A → B} → f ≣ f
refl≣ _ = refl

sym≣ : {A B : Set} {f g : A → B} →
  f ≣ g → g ≣ f
sym≣ p a = sym (p a)

trans≣ : {A B : Set} {f g h : A → B} →
  f ≣ g → g ≣ h → f ≣ h
trans≣ p q a = trans (p a) (q a)

----------------------------------------------------------------------

Equivalence≣ : {A B : Set} → Equivalence {A → B} _≣_
Equivalence≣ = record
  { refl≈  = refl≣
  ; sym≈   = sym≣
  ; trans≈ = trans≣
  }

----------------------------------------------------------------------