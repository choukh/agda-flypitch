{-# OPTIONS --cubical-compatible --safe #-}

open import FOL.Signature
module FOL.Lemmas.Realization {u} (σ : Signature {u}) where
open import FOL.Base (σ) hiding (⊥-elim; subst)
open import FOL.Lemmas.Lifting (σ)
open import FOL.Lemmas.Substitution (σ)
open import FOL.Realization (σ)
open Structure

open import Data.Nat
open import Data.Empty using (⊥-elim)
open import Data.Vec using (Vec; []; _∷_)
open import Function using (_$_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality.Core as Eq
  using (_≡_; refl; sym; cong; subst)
open import StdlibExt.Data.Vec using ([]-refl)
open import StdlibExt.Data.Nat.Properties
open import StdlibExt.Relation.Binary.PropositionalEquivalence u
  renaming (begin_ to begin↔_; _∎ to _∎↔) hiding (sym)
open Eq.≡-Reasoning

module PreRealizationLemmas (𝒮 : Structure σ) where
  open PreRealization 𝒮 renaming (realizeₜ to rₜ; realize to r)

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
  realizeₜ-subst 𝓋 n (var k) s xs with <-cmp k n
  ... | tri< _ _ _ = refl
  ... | tri> _ _ _ = refl
  ... | tri≈ _ _ _ = cong (rₜ 𝓋 (s ↑[ 0 ] n)) ([]-refl xs)
  realizeₜ-subst 𝓋 n (func f) s xs = refl
  realizeₜ-subst 𝓋 n (app t₁ t₂) s xs =
    let 𝓋' = 𝓋 [ rₜ 𝓋 (s ↑ n) [] / n ]ᵥ in              begin
    rₜ 𝓋' t₁             (rₜ 𝓋' t₂ [] ∷ xs)             ≡⟨ cong (rₜ 𝓋' t₁) $ cong (_∷ xs) (realizeₜ-subst 𝓋 n t₂ s []) ⟩
    rₜ 𝓋' t₁             (rₜ 𝓋 (t₂ [ s / n ]ₜ) [] ∷ xs) ≡⟨ realizeₜ-subst 𝓋 n t₁ s _ ⟩
    rₜ 𝓋 (t₁ [ s / n ]ₜ) (rₜ 𝓋 (t₂ [ s / n ]ₜ) [] ∷ xs) ∎

  realizeₜ-subst-lift : ∀ {l} (𝓋 : ℕ → 𝒮 .carrier) (n : ℕ) (t : Termₙ l)
    (x : 𝒮 .carrier) (xs : Vec (𝒮 .carrier) l)
    → rₜ (𝓋 [ x / n ]ᵥ) (t ↑[ n ] 1) xs ≡ rₜ 𝓋 t xs
  realizeₜ-subst-lift 𝓋 n (var k) x xs with <-cmp k n | k <? n
  ... | tri≈ ¬p _ _ | yes p = ⊥-elim $ ¬p p
  ... | tri> ¬p _ _ | yes p = ⊥-elim $ ¬p p
  ... | tri< p ¬q _ | yes _ with <-cmp k n
  ... | tri≈ _ q _  = ⊥-elim $ ¬q q
  ... | tri> ¬p _ _ = ⊥-elim $ ¬p p
  ... | tri< _ _ _  = refl
  realizeₜ-subst-lift 𝓋 n (var k) x xs | _ | no ¬p with <-cmp (k + 1) n
  ... | tri< q _ _    = ⊥-elim $ ¬p (<-trans n<n+1 q)
  ... | tri≈ _ refl _ = ⊥-elim $ ¬p (subst (_≤ k + 1) (+-comm k 1) ≤-refl)
  ... | tri> _ _ _    = cong 𝓋 (m+n∸n≡m k 1)
  realizeₜ-subst-lift 𝓋 n (func f) x xs = refl
  realizeₜ-subst-lift 𝓋 n (app t₁ t₂) x xs =
    let 𝓋' = 𝓋 [ x / n ]ᵥ in                          begin
    rₜ 𝓋' (t₁ ↑[ n ] 1) (rₜ 𝓋' (t₂ ↑[ n ] 1) [] ∷ xs) ≡⟨ realizeₜ-subst-lift 𝓋 n t₁ x _ ⟩
    rₜ 𝓋 t₁             (rₜ 𝓋' (t₂ ↑[ n ] 1) [] ∷ xs) ≡⟨ cong (rₜ 𝓋 t₁) $ cong (_∷ xs) (realizeₜ-subst-lift 𝓋 n t₂ x []) ⟩
    rₜ 𝓋 t₁             (rₜ 𝓋 t₂ [] ∷ xs)             ∎

  realize-cong : ∀ {l} (𝓋 𝓊 : ℕ → 𝒮 .carrier) (ext : ∀ n → 𝓋 n ≡ 𝓊 n)
    (φ : Formulaₙ l) (xs : Vec (𝒮 .carrier) l)
    → r 𝓋 φ xs ↔ r 𝓊 φ xs
  realize-cong 𝓋 𝓊 ext ⊥           xs = id
  realize-cong 𝓋 𝓊 ext (rel R)     xs = id
  realize-cong 𝓋 𝓊 ext (appᵣ φ t)  xs
    rewrite realizeₜ-cong 𝓋 𝓊 ext t [] = realize-cong 𝓋 𝓊 ext φ _
  realize-cong 𝓋 𝓊 ext (t₁ ≈ t₂) xs
    rewrite realizeₜ-cong 𝓋 𝓊 ext t₁ xs
          | realizeₜ-cong 𝓋 𝓊 ext t₂ xs = id
  realize-cong 𝓋 𝓊 ext (φ₁ ⇒ φ₂) xs =
    →-cong (realize-cong 𝓋 𝓊 ext φ₁ xs) (realize-cong 𝓋 𝓊 ext φ₂ xs)
  realize-cong 𝓋 𝓊 ext (∀' φ) xs = ∀-cong $ λ x
    → realize-cong (𝓋 [ x / 0 ]ᵥ) (𝓊 [ x / 0 ]ᵥ) (/ᵥ-cong ext x 0) φ xs

  realize-subst : ∀ {l} (𝓋 : ℕ → 𝒮 .carrier) (n : ℕ) (φ : Formulaₙ l)
    (s : Term) (xs : Vec (𝒮 .carrier) l)
    → r (𝓋 [ rₜ 𝓋 (s ↑ n) [] / n ]ᵥ) φ xs ↔ r 𝓋 (φ [ s / n ]) xs
  realize-subst 𝓋 n ⊥          s xs = id
  realize-subst 𝓋 n (rel r₁)   s xs = id
  realize-subst 𝓋 n (appᵣ φ t) s xs
    rewrite realizeₜ-subst 𝓋 n t s [] = realize-subst 𝓋 n φ s _
  realize-subst 𝓋 n (t₁ ≈ t₂) s xs
    rewrite realizeₜ-subst 𝓋 n t₁ s xs
          | realizeₜ-subst 𝓋 n t₂ s xs = id
  realize-subst 𝓋 n (φ₁ ⇒ φ₂) s xs =
    →-cong (realize-subst 𝓋 n φ₁ s xs) (realize-subst 𝓋 n φ₂ s xs)
  realize-subst 𝓋 n (∀' φ) s xs = ∀-cong $ λ x →
    let t₁ = rₜ (𝓋 [ x / 0 ]ᵥ) (s ↑ suc n)   []
        t₂ = rₜ (𝓋 [ x / 0 ]ᵥ) ((s ↑ n) ↑ 1) []
        𝓋₁ = 𝓋 [ t₁ / n ]ᵥ [ x / 0 ]ᵥ
        𝓋₂ = 𝓋 [ t₂ / n ]ᵥ [ x / 0 ]ᵥ
        t≡ : t₂ ≡ t₁
        t≡ = cong (λ t → rₜ (𝓋 [ x / 0 ]ᵥ) t []) (↑↑˘ s n 1)
        𝓋≡₁ : ∀ m → 𝓋₂ m ≡ 𝓋₁ m
        𝓋≡₁ m = cong (λ t → (𝓋 [ t / n ]ᵥ [ x / 0 ]ᵥ) m) t≡
        𝓋₃ = 𝓋 [ rₜ 𝓋 (s ↑ n) [] / n ]ᵥ [ x / 0 ]ᵥ
        𝓋≡₂ : ∀ m → 𝓋₃ m ≡ 𝓋₂ m
        𝓋≡₂ m = sym $ cong (λ t → (𝓋 [ t / n ]ᵥ [ x / 0 ]ᵥ) m) (realizeₜ-subst-lift 𝓋 0 (s ↑ n) x [])
    in begin↔
    r 𝓋₃ φ xs                             ≈⟨ realize-cong _ _ 𝓋≡₂ φ xs ⟩
    r 𝓋₂ φ xs                             ≈⟨ realize-cong _ _ 𝓋≡₁ φ xs ⟩
    r 𝓋₁ φ xs                             ≈⟨ realize-cong _ _ (//ᵥ 𝓋 x t₁ 0 n) φ xs ⟩
    r (𝓋 [ x / 0 ]ᵥ [ t₁ / suc n ]ᵥ) φ xs ≈⟨ realize-subst (𝓋 [ x / 0 ]ᵥ) (suc n) φ s xs ⟩
    r (𝓋 [ x / 0 ]ᵥ) (φ [ s / suc n ]) xs ∎↔
