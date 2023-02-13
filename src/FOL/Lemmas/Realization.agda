{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS -W noUnsupportedIndexedMatch #-}

open import FOL.Signature
module FOL.Lemmas.Realization {u} (σ : Signature {u}) where
open import FOL.Base (σ) hiding (⊥-elim)
open import FOL.Realization (σ)
open Structure

open import Data.Empty using (⊥-elim)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec using (Vec; []; _∷_)
open import Function using (_$_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality.Core as Eq using (_≡_; refl; cong)
open import StdlibExt.Data.Vec using ([]-refl)
open import StdlibExt.Data.Nat.Properties using (n<n+1)
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
  realizeₜ-subst 𝓋 n (var k) s xs with k <? n
  ... | yes _ = refl
  ... | no  _ with n <? k
  ... | yes _ = refl
  ... | no  _ = cong (rₜ 𝓋 (s ↑[ 0 ] n)) ([]-refl xs)
  realizeₜ-subst 𝓋 n (func f) s xs = refl
  realizeₜ-subst 𝓋 n (app t₁ t₂) s xs =
    let 𝓋' = 𝓋 [ rₜ 𝓋 (s ↑ n) [] / n ]ᵥ in              begin
    rₜ 𝓋' (app t₁ t₂) xs                                ≡⟨⟩
    rₜ 𝓋' t₁             (rₜ 𝓋' t₂ [] ∷ xs)             ≡⟨ cong (rₜ 𝓋' t₁) $ cong (_∷ xs) (realizeₜ-subst 𝓋 n t₂ s []) ⟩
    rₜ 𝓋' t₁             (rₜ 𝓋 (t₂ [ s / n ]ₜ) [] ∷ xs) ≡⟨ realizeₜ-subst 𝓋 n t₁ s _ ⟩
    rₜ 𝓋 (t₁ [ s / n ]ₜ) (rₜ 𝓋 (t₂ [ s / n ]ₜ) [] ∷ xs) ≡⟨⟩
    rₜ 𝓋 (app t₁ t₂ [ s / n ]ₜ) xs                      ∎

  realizeₜ-subst-lift : ∀ {l} (𝓋 : ℕ → 𝒮 .carrier) (n : ℕ) (t : Termₙ l)
    (x : 𝒮 .carrier) (xs : Vec (𝒮 .carrier) l)
    → rₜ (𝓋 [ x / n ]ᵥ) (t ↑[ n ] 1) xs ≡ rₜ 𝓋 t xs
  realizeₜ-subst-lift 𝓋 n (var k) x xs with k <? n
  ... | yes p with k <? n
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p p)
  realizeₜ-subst-lift 𝓋 n (var k) x xs | no ¬p with k + 1 <? n
  ... | yes q = ⊥-elim (¬p (<-trans n<n+1 q))
  ... | no ¬q with n <? k + 1
  ... | yes r = cong 𝓋 (m+n∸n≡m k 1)
  ... | no ¬r = ⊥-elim (¬p (≰⇒> λ n≤k → ¬r (≤-trans (s≤s n≤k) n<n+1)))
  realizeₜ-subst-lift 𝓋 n (func f) x xs = refl
  realizeₜ-subst-lift 𝓋 n (app t₁ t₂) x xs =
    let 𝓋' = 𝓋 [ x / n ]ᵥ in                          begin
    rₜ 𝓋' (app t₁ t₂ ↑[ n ] 1) xs                     ≡⟨⟩
    rₜ 𝓋' (t₁ ↑[ n ] 1) (rₜ 𝓋' (t₂ ↑[ n ] 1) [] ∷ xs) ≡⟨ realizeₜ-subst-lift 𝓋 n t₁ x _ ⟩
    rₜ 𝓋 t₁             (rₜ 𝓋' (t₂ ↑[ n ] 1) [] ∷ xs) ≡⟨ cong (rₜ 𝓋 t₁) $ cong (_∷ xs) (realizeₜ-subst-lift 𝓋 n t₂ x []) ⟩
    rₜ 𝓋 t₁             (rₜ 𝓋 t₂ [] ∷ xs)             ≡⟨⟩
    rₜ 𝓋 (app t₁ t₂) xs                               ∎
