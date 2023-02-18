{-# OPTIONS --cubical-compatible --safe #-}

module StdlibExt.Relation.Binary.PropositionalEquivalence (u) where

open import Level
open import Function using (_$_)
open import Function.Equality using (_⟨$⟩_) public
open import Function.Equivalence
  renaming (_⇔_ to _↔_; ⇔-setoid to ↔-setoid; equivalence to mk↔) public
open import Relation.Binary.Reasoning.Setoid (↔-setoid u)
  using (begin_; step-≈; step-≈˘; _∎) public
open Equivalence public

private variable
  a b c d : Level
  A : Set a
  B : Set b
  C : Set c
  D : Set d
  f : A → Set b
  g : A → Set c

∀-cong : (∀ x → f x ↔ g x) → (∀ x → f x) ↔ (∀ x → g x)
∀-cong ↔ = mk↔ (λ f x → to   (↔ x) ⟨$⟩ f x)
               (λ g x → from (↔ x) ⟨$⟩ g x)

→-cong : A ↔ B → C ↔ D → (A → C) ↔ (B → D)
→-cong ↔₁ ↔₂ = mk↔ (λ f x → to   ↔₂ ⟨$⟩ (f $ from ↔₁ ⟨$⟩ x))
                   (λ g x → from ↔₂ ⟨$⟩ (g $ to   ↔₁ ⟨$⟩ x))
