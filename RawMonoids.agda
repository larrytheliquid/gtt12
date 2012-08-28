open import Prelude
open import Data.Bool
open import Data.Nat
open import Data.List
module RawMonoids where

record RawMonoid (S : Set) : Set₁ where
  field
    ı : S
    _∙_ : (x y : S) → S

  mconcat : List S → S
  mconcat [] = ı
  mconcat (x ∷ xs) = x ∙ mconcat xs

----------------------------------------------------------------------

RawMonoidBool : RawMonoid Bool
RawMonoidBool = record
  { ı = false
  ; _∙_ = _∨_
  }

RawMonoidℕ : RawMonoid ℕ
RawMonoidℕ = record
  { ı = zero
  ; _∙_ = _+_
  }

----------------------------------------------------------------------

mconcat′ : ∀{A} → RawMonoid A → List A → A
mconcat′ mon [] = RawMonoid.ı mon
mconcat′ mon (x ∷ xs) = RawMonoid._∙_ mon x (mconcat′ mon xs)

----------------------------------------------------------------------

mconcat′′ : ∀{A} → RawMonoid A → List A → A
mconcat′′ mon [] = ı
  where open RawMonoid mon
mconcat′′ mon (x ∷ xs) = x ∙ mconcat′′ mon xs
  where open RawMonoid mon

----------------------------------------------------------------------

open RawMonoid {{...}}

mconcat′′′ : ∀{A} {{ mon : RawMonoid A}} → List A → A
mconcat′′′ [] = ı
mconcat′′′ (x ∷ xs) = x ∙ mconcat′′′ xs

