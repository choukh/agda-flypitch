{-# OPTIONS --cubical-compatible --safe #-}

open import FOL.Signature
module FOL.Bounded.Substitution (ℒ : Signature {u}) where
open import FOL.Bounded.Base ℒ hiding (n)
open import FOL.Bounded.Casting ℒ

open import Data.Fin using (Fin; toℕ; fromℕ<; reduce≥)
open import Data.Nat using (ℕ; suc; _+_; s≤s; z≤n)
open import Data.Nat.Properties
open import Function using (_$_)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

substₜ : ∀ {m} n (t : Termₗ (suc m + n) l) (s : Term n) → Termₗ (m + n) l
substₜ n (var k) s with <-cmp (toℕ k) n
... | tri< k<n _ _  = var $ fromℕ< $ ≤-trans k<n (m≤n+m _ _)
... | tri≈ _ _ _    = castₜ (m≤n+m _ _) s --TODO: use (s ↑ n) here
... | tri> _ _ n<k  = var (reduce≥ k (≤-trans (s≤s z≤n) n<k))
substₜ n (func f) s = func f
substₜ n (app t₁ t₂) s = app (substₜ n t₁ s) (substₜ n t₂ s)

syntax substₜ n t s = t [ s / n ]ₜ
