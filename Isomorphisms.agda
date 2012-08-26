open import Prelude
open import Data.Bool
open import Data.Nat
open import Monoids
module Isomorphisms where

record Isomorphism {S T : Set} (to : S → T) : Set where
  field
    from : T → S
    from∘to≡id : (s : S) → (from ∘ to) s ≡ s
    to∘from≡id : (t : T) → (to ∘ from) t ≡ t
open Isomorphism

isos-uniq : ∀ {S T} (to : S → T) (f g : Isomorphism to) (t : T) →
  from f t ≡ from g t
isos-uniq to f g t =
  from f t                 ≡⟨ sym $ from∘to≡id g (from f t) ⟩
  (from g ∘ to) (from f t) ≡⟨ cong (from g) (to∘from≡id f t) ⟩
  from g t                 ∎
