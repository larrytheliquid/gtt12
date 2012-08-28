open import Prelude
open import Data.Bool
open import Data.Nat
module Monoids where

----------------------------------------------------------------------

false∨b≡b : (b : Bool) →
  false ∨ b ≡ b
false∨b≡b b = refl

b∨false≡b : (b : Bool) →
  b ∨ false ≡ b
b∨false≡b true = refl
b∨false≡b false = refl

∨assoc : (x y z : Bool) →
  x ∨ (y ∨ z) ≡ (x ∨ y) ∨ z
∨assoc true y z = refl
∨assoc false y z = refl

----------------------------------------------------------------------

0+n≡n : (n : ℕ) →
  zero + n ≡ n
0+n≡n n = refl

n+0≡n : (n : ℕ) →
  n + zero ≡ n
n+0≡n zero = refl
n+0≡n (suc n) = cong suc (n+0≡n n)

+assoc : (x y z : ℕ) →
  x + (y + z) ≡ (x + y) + z
+assoc zero y z = refl
+assoc (suc x) y z = cong suc (+assoc x y z)

----------------------------------------------------------------------

record Monoid (S : Set) : Set₁ where
  infixr 9 _∙_
  field
    ı : S
    _∙_ : (x y : S) → S

    identl : (x : S) → ı ∙ x ≡ x
    identr : (x : S) → x ∙ ı ≡ x
    assoc : (x y z : S) →
      x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z

----------------------------------------------------------------------

MonoidBool : Monoid Bool
MonoidBool = record
  { ı = false
  ; _∙_ = _∨_
  ; identl = false∨b≡b
  ; identr = b∨false≡b
  ; assoc = ∨assoc
  }

Monoidℕ : Monoid ℕ
Monoidℕ = record
  { ı = zero
  ; _∙_ = _+_
  ; identl = 0+n≡n
  ; identr = n+0≡n
  ; assoc = +assoc
  }

----------------------------------------------------------------------

