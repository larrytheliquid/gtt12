open import Prelude
open import Data.Bool
open import Data.Nat
open import Data.List
module RawMonoids where

record RawMonoid (S : Set) : Set₁ where
  field
    e : S
    _∙_ : (x y : S) → S

RawMonoid∶Bool/false/∨ : RawMonoid Bool
RawMonoid∶Bool/false/∨ = record
  { e = false
  ; _∙_ = _∨_
  }

RawMonoid∶ℕ/0/+ : RawMonoid ℕ
RawMonoid∶ℕ/0/+ = record
  { e = zero
  ; _∙_ = _+_
  }

mconcat : ∀{A} → RawMonoid A → List A → A
mconcat mon [] = RawMonoid.e mon
mconcat mon (x ∷ xs) = RawMonoid._∙_ mon x (mconcat mon xs)

mconcat′ : ∀{A} → RawMonoid A → List A → A
mconcat′ mon [] = e
  where open RawMonoid mon
mconcat′ mon (x ∷ xs) = x ∙ mconcat′ mon xs
  where open RawMonoid mon

open RawMonoid {{...}}

mconcat′′ : ∀{A} {{ mon : RawMonoid A}} → List A → A
mconcat′′ [] = e
mconcat′′ (x ∷ xs) = x ∙ mconcat′′ xs

