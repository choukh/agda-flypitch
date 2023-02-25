{-# OPTIONS --cubical-compatible --safe #-}

open import FOL.Signature
module FOL.Bounded.Lifting (ℒ : Signature {u}) where
open import FOL.Bounded.Base ℒ

open import Data.Fin using (Fin; toℕ; fromℕ<; _↑ˡ_)
open import Data.Nat using (ℕ; _+_; _<?_)
open import Data.Nat.Properties
open import Relation.Nullary using (Dec; yes; no)

_↑[_]_ : ∀ (t : Termₗ n l) → (m n' : ℕ) → Termₗ (n + n') l
var k     ↑[ m ] n' with toℕ k <? m
... | yes p = var (k ↑ˡ n')
... | no ¬p = var {!   !}
func f    ↑[ m ] n' = func f
app t₁ t₂ ↑[ m ] n' = app (t₁ ↑[ m ] n') (t₂ ↑[ m ] n')
