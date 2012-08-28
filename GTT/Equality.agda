module GTT.Equality where

infix  2 _∎ _≡_
infixr 2 _≡⟨_⟩_
infixr 3 _$_
infixr 9 _∘_

----------------------------------------------------------------------

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : {A B : Set} {x y : A} (f : A → B) →
  x ≡ y → f x ≡ f y
cong f refl = refl

----------------------------------------------------------------------

_∎ : {A : Set} (a : A) → a ≡ a
_ ∎ = refl

_≡⟨_⟩_ : {A : Set} (x : A) {y z : A} →
  x ≡ y → y ≡ z → x ≡ z
_ ≡⟨ ab ⟩ bc = trans ab bc

----------------------------------------------------------------------

_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
_∘_ g f a = g (f a)

_$_ : {A B : Set} → (A → B) → (A → B)
f $ x = f x

id : {A : Set} → A → A
id a = a

----------------------------------------------------------------------
