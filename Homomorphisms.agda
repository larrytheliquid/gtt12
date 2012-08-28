open import Prelude
open import Data.Bool
open import Data.Nat
open import Monoids
module Homomorphisms where

----------------------------------------------------------------------

gtz : ℕ → Bool
gtz zero = false
gtz (suc _) = true

gtz0≡false : gtz 0 ≡ false
gtz0≡false = refl

gtz-preserves+ : (m n : ℕ) →
  gtz (m + n) ≡ gtz m ∨ gtz n
gtz-preserves+ zero _ = refl
gtz-preserves+ (suc _) _ = refl

----------------------------------------------------------------------

kf : ℕ → Bool
kf _ = false

kf0≡false : kf 0 ≡ false
kf0≡false = refl

kf-preserves+ : (m n : ℕ) →
  kf (m + n) ≡ kf m ∨ kf n
kf-preserves+ _ _ = refl

----------------------------------------------------------------------

record Homomorphism {S S′} (M : Monoid S) (M′ : Monoid S′) : Set₁ where
  open Monoid M
  open Monoid M′ renaming ( ı to ı′ ; _∙_ to _∙′_ )
  field
    f : S → S′
    preserves-ı : f ı ≡ ı′
    preserves-∙ : (x y : S) →
      f (x ∙ y) ≡ f x ∙′ f y

----------------------------------------------------------------------

record Homomorphism′ {S S′} (M : Monoid S) (M′ : Monoid S′) : Set₁ where
  open Monoid {{...}}
  field
    f : S → S′
    preserves-ı : f ı ≡ ı
    preserves-∙ : (x y : S) →
      f (x ∙ y) ≡ f x ∙ f y

----------------------------------------------------------------------

Homomorphism∶gtz : Homomorphism Monoidℕ MonoidBool
Homomorphism∶gtz = record
  { f = gtz
  ; preserves-ı = gtz0≡false
  ; preserves-∙ = gtz-preserves+
  }

Homomorphism∶kf : Homomorphism Monoidℕ MonoidBool
Homomorphism∶kf = record
  { f = kf
  ; preserves-ı = kf0≡false
  ; preserves-∙ = kf-preserves+
  }

----------------------------------------------------------------------

kt : ℕ → Bool
kt n = true

kt-natural-for-gtz-kf : (m n o : ℕ) →
  kt (m + n + o) ≡ gtz m ∨ kt n ∨ kf o
kt-natural-for-gtz-kf zero n o = refl
kt-natural-for-gtz-kf (suc m) n o = refl

----------------------------------------------------------------------

record NaturalTransformation {S S′} {M : Monoid S} {M′ : Monoid S′}
  (F G : Homomorphism M M′) : Set₁ where
  open Homomorphism F
  open Homomorphism G renaming ( f to f′ )
  open Monoid {{...}}
  field
    g : S → S′
    natural : (x y z : S) →
      g (x ∙ y ∙ z) ≡ f x ∙ g y ∙ f′ z

----------------------------------------------------------------------

NaturalTransformation∶kt-gtz-kf : NaturalTransformation Homomorphism∶gtz Homomorphism∶kf
NaturalTransformation∶kt-gtz-kf = record
  { g = kt
  ; natural = kt-natural-for-gtz-kf
  }

----------------------------------------------------------------------
