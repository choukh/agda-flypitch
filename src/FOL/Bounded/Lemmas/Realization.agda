{-# OPTIONS --cubical-compatible --safe #-}

open import FOL.Signature
open import FOL.Interpretation using (Interpretation)
module FOL.Bounded.Lemmas.Realization {u} (σ : Signature {u}) (𝒮 : Interpretation σ) where

open import FOL.Bounded.Base σ
open import FOL.Bounded.Interpretation σ
import FOL.Interpretation σ as Free
open FOL.Interpretation.Interpretation

open import Data.Nat
open import Data.Fin using (Fin; toℕ)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Preₜ where
  open PreRealizer 𝒮 using () renaming (realizeₜ to rₜ; realize to r) public
  open Free.PreRealizer 𝒮 using () renaming (realizeₜ to 𝑟ₜ; realize to 𝑟) public

  realizeₜ-eq : ∀ (𝓋 : Vec (𝒮 .domain) n) (𝑣 : ℕ → 𝒮 .domain)
    (eq : ∀ k → lookup 𝓋 k ≡ 𝑣 (toℕ k))
    (t : Termₗ n l) (xs : Vec (𝒮 .domain) l)
    → rₜ 𝓋 t xs ≡ 𝑟ₜ 𝑣 (unboundₜ t) xs
  realizeₜ-eq 𝓋 𝑣 eq (var k)     xs = eq k
  realizeₜ-eq 𝓋 𝑣 eq (func f)    xs = refl
  realizeₜ-eq 𝓋 𝑣 eq (app t₁ t₂) xs rewrite realizeₜ-eq 𝓋 𝑣 eq t₂ [] = realizeₜ-eq 𝓋 𝑣 eq t₁ _
