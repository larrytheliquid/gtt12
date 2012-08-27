open import Prelude
open import Data.Bool
open import Data.Nat
open import Monoids
module CommutativeMonoids where

record CommutativeMonoid (S : Set) : Set₁ where
  infixr 9 _∙_
  field
    e : S
    _∙_ : (x y : S) → S

    identl : (x : S) → e ∙ x ≡ x
    identr : (x : S) → x ∙ e ≡ x
    assoc : (x y z : S) →
      x ∙ (y ∙ z) ≡ (x ∙ y) ∙ z
    commut : (x y : S) →
      x ∙ y ≡ y ∙ x

----------------------------------------------------------------------

record CommutativeMonoid′ (S : Set) : Set₁ where
  field
    monoid : Monoid S
    commut : let open Monoid monoid in
      (x y : S) → x ∙ y ≡ y ∙ x
  open Monoid monoid public

----------------------------------------------------------------------

record CommutativeMonoid′′ (S : Set) : Set₁ where
  field monoid : Monoid S
  open Monoid monoid
  field commut : (x y : S) → x ∙ y ≡ y ∙ x
  open Monoid monoid public

----------------------------------------------------------------------

+commut : (x y : ℕ) →
  x + y ≡ y + x
+commut zero y = sym (n+0≡n y)
+commut (suc x) y = trans (cong suc (+commut x y)) (lemma y x)
  where
  lemma : (a b : ℕ) → suc (a + b) ≡ a + suc b
  lemma zero _ = refl
  lemma (suc a) b = cong suc (lemma a b)

----------------------------------------------------------------------

+commut′ : (x y : ℕ) →
  x + y ≡ y + x

+commut′ zero y = 
  zero + y ≡⟨ refl ⟩
  y        ≡⟨ sym (n+0≡n y) ⟩
  y + 0    ∎

+commut′ (suc x) y =
  suc x + y   ≡⟨ refl ⟩
  suc (x + y) ≡⟨ cong suc ih ⟩
  suc (y + x) ≡⟨ lemma y x ⟩
  y + suc x   ∎ where

  ih : x + y ≡ y + x
  ih = +commut′ x y

  lemma : (a b : ℕ) → suc (a + b) ≡ a + suc b
  lemma zero _ = refl
  lemma (suc a) b = cong suc (lemma a b)

----------------------------------------------------------------------

CommutativeMonoidℕ : CommutativeMonoid′ ℕ
CommutativeMonoidℕ = record
  { monoid = Monoidℕ
  ; commut = +commut
  }
