{-# OPTIONS --cubical-compatible --safe #-}

open import FOL.Signature
module FOL.Lemmas.Realization {u} (σ : Signature {u}) where
open import FOL.Base (σ)
open import FOL.Realization (σ)
open Structure

open import Data.Bool using (true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _∸_; _<ᵇ_)
open import Data.Vec using (Vec; []; _∷_)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality.Core as Eq using (_≡_; refl; cong)
open import StdlibExt.Data.Vec using ([]-refl)
open Eq.≡-Reasoning

module PreRealizationLemmas (𝒮 : Structure σ) where
  open PreRealization 𝒮 renaming (realizeₜ to rₜ)

  realizeₜ-cong : ∀ {l} (𝓋 𝓊 : ℕ → 𝒮 .carrier) (ext : ∀ n → 𝓋 n ≡ 𝓊 n)
    (t : Termₙ l) (xs : Vec (𝒮 .carrier) l)
    → rₜ 𝓋 t xs ≡ rₜ 𝓊 t xs
  realizeₜ-cong 𝓋 𝓊 ext (var k)     xs = ext k
  realizeₜ-cong 𝓋 𝓊 ext (func f)    xs = refl
  realizeₜ-cong 𝓋 𝓊 ext (app t₁ t₂) xs
    rewrite realizeₜ-cong 𝓋 𝓊 ext t₂ []
    rewrite realizeₜ-cong 𝓋 𝓊 ext t₁ (rₜ 𝓊 t₂ [] ∷ xs) = refl

  realizeₜ-subst : ∀ {l} (𝓋 : ℕ → 𝒮 .carrier) (n : ℕ) (t : Termₙ l)
    (s : Term) (xs : Vec (𝒮 .carrier) l)
    → rₜ (𝓋 [ rₜ 𝓋 (s ↑ n) [] / n ]ᵥ) t xs ≡ rₜ 𝓋 (t [ s / n ]ₜ) xs
  realizeₜ-subst 𝓋 n (var k) s xs with k <ᵇ n
  ... | true  = refl
  ... | false with n <ᵇ k
  ... | true  = refl
  ... | false = cong (rₜ 𝓋 (s ↑[ 0 ] n)) ([]-refl xs)
  realizeₜ-subst 𝓋 n (func f) s xs = refl
  realizeₜ-subst 𝓋 n (app t₁ t₂) s xs =
    let 𝓋' = 𝓋 [ rₜ 𝓋 (s ↑ n) [] / n ]ᵥ in              begin
    rₜ 𝓋' (app t₁ t₂) xs                                ≡⟨⟩
    rₜ 𝓋' t₁             (rₜ 𝓋' t₂ [] ∷ xs)             ≡⟨ cong (rₜ 𝓋' t₁) $ cong (_∷ xs) (realizeₜ-subst 𝓋 n t₂ s []) ⟩
    rₜ 𝓋' t₁             (rₜ 𝓋 (t₂ [ s / n ]ₜ) [] ∷ xs) ≡⟨ realizeₜ-subst 𝓋 n t₁ s _ ⟩
    rₜ 𝓋 (t₁ [ s / n ]ₜ) (rₜ 𝓋 (t₂ [ s / n ]ₜ) [] ∷ xs) ≡⟨⟩
    rₜ 𝓋 (app t₁ t₂ [ s / n ]ₜ) xs                      ∎