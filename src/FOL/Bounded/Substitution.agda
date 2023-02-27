{-# OPTIONS --cubical-compatible --safe #-}

open import FOL.Signature
module FOL.Bounded.Substitution (ℒ : Signature {u}) where
open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Casting ℒ
open import FOL.Bounded.Lifting ℒ

open import Data.Fin using (Fin; toℕ; fromℕ<; reduce≥)
open import Data.Nat using (ℕ; suc; _+_; s≤s; z≤n; _≤_)
open import Data.Nat.Properties
open import Function using (_$_)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl) renaming (subst to ≡-subst)

substₜ : ∀ {n m l} (t : Termₗ (suc n + m) l) (s : Term m) → Termₗ (n + m) l
substₜ {n} {m} (var k) s with <-cmp (toℕ k) n
... | tri< k<n _ _  = var $ fromℕ< $ ≤-trans k<n (m≤m+n _ _)
... | tri≈ _ _ _    = castₜ (≡-subst (_≤ n + m) (+-comm n _) ≤-refl) (s ↑ n)
... | tri> _ _ n<k  = var (reduce≥ k (≤-trans (s≤s z≤n) n<k))
substₜ (func f) s = func f
substₜ (app t₁ t₂) s = app (substₜ t₁ s) (substₜ t₂ s)

syntax substₜ {n} t s = t [ s / n ]ₜ

subst : ∀ {n m l} (φ : Formulaₗ (suc n + m) l) (s : Term m) → Formulaₗ (n + m) l
subst ⊥ s = ⊥
subst (rel R) s = rel R
subst (appᵣ φ t) s = appᵣ (subst φ s) (substₜ t s)
subst (t₁ ≈ t₂) s = substₜ t₁ s ≈ substₜ t₂ s
subst (φ₁ ⇒ φ₂) s = subst φ₁ s ⇒ subst φ₂ s
subst (∀' φ) s = ∀' subst φ s

syntax subst {n} φ s = φ [ s / n ]
