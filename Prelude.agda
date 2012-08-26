module Prelude where

infix 4 _≡_

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

cong : {A B : Set} {x y : A} (f : A → B) →
  x ≡ y → f x ≡ f y
cong f refl = refl

infix  3 _×_
infixr 4 _,_

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    π₁ : A
    π₂ : B
open _×_ public

curry : {A B C : Set} → (A × B → C) → A → B → C
curry f a b = f (a , b)

uncurry : {A B C : Set} → (A → B → C) → A × B → C
uncurry f (a , b) = f a b
