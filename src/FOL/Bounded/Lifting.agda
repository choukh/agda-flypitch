{-# OPTIONS --cubical-compatible --safe #-}

open import FOL.Language
module FOL.Bounded.Lifting (ℒ : Language {u}) where
open import FOL.Bounded.Base ℒ

open import Data.Fin using (Fin; toℕ; cast; fromℕ<; _↑ˡ_; _↑ʳ_)
open import Data.Nat using (ℕ; _+_; _<?_)
open import Data.Nat.Properties
open import Relation.Nullary using (Dec; yes; no)

_↑[_]_ : ∀ (t : Termₗ n l) → (m n' : ℕ) → Termₗ (n + n') l
var k     ↑[ m ] n' with toℕ k <? m
... | yes _ = var (k ↑ˡ n')
... | no  _ = var (cast (+-comm n' _) (n' ↑ʳ k))
func f    ↑[ m ] n' = func f
app t₁ t₂ ↑[ m ] n' = app (t₁ ↑[ m ] n') (t₂ ↑[ m ] n')

_↑_ : ∀ (t : Termₗ n l) → (n' : ℕ) → Termₗ (n + n') l
t ↑ n' = t ↑[ 0 ] n'
