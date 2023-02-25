{-# OPTIONS --cubical-compatible --safe #-}

open import FOL.Signature
module FOL.Bounded.Casting (ℒ : Signature {u}) where
open import FOL.Bounded.Base ℒ hiding (n)

open import Data.Fin using (Fin; inject≤)
open import Data.Nat using (ℕ; _≤_)
open import Data.Sum.Base using (inj₁; inj₂)

private variable
  m n : ℕ

castₜ : m ≤ n → Termₗ m l → Termₗ n l
castₜ m≤n (var k)     = var (inject≤ k m≤n)
castₜ m≤n (func f)    = func f
castₜ m≤n (app t₁ t₂) = app (castₜ m≤n t₁) (castₜ m≤n t₂)
