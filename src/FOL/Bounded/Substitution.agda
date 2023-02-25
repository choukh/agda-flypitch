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

substₜ : ∀ {m l} n (t : Termₗ (suc m + n) l) (s : Term n) → Termₗ (m + n) l
substₜ {m} n (var k) s with <-cmp (toℕ k) m
... | tri< k<n _ _  = var $ fromℕ< $ ≤-trans k<n (m≤m+n _ _)
... | tri≈ _ _ _    = castₜ (≡-subst (_≤ m + n) (+-comm m _) ≤-refl) (s ↑ m)
... | tri> _ _ n<k  = var (reduce≥ k (≤-trans (s≤s z≤n) n<k))
substₜ n (func f) s = func f
substₜ n (app t₁ t₂) s = app (substₜ n t₁ s) (substₜ n t₂ s)

syntax substₜ n t s = t [ s / n ]ₜ
