{-# OPTIONS --cubical-compatible --safe #-}

open import FOL.Signature
module FOL.Lemmas.Lifting {u} (σ : Signature {u}) where
open import FOL.Base (σ) hiding (⊥-elim)

open import Data.Nat
open import Data.Nat.Properties
open import Data.Empty using (⊥-elim)
open import Function using (_$_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong)

↑[]↑[] : ∀ {l} (t : Termₙ l) (n₁ m₁ n₂ m₂ : ℕ) → m₁ ≤ m₂ → m₂ ≤ m₁ + n₁
  → (t ↑[ m₁ ] n₁) ↑[ m₂ ] n₂ ≡ t ↑[ m₁ ] (n₁ + n₂)
↑[]↑[] (var k) n₁ m₁ n₂ m₂ ≤₁ ≤₂ with k <? m₁
... | yes p with k <? m₂
... | yes _ = refl
... | no ¬q = ⊥-elim $ ¬q $ ≤-trans p ≤₁
↑[]↑[] (var k) n₁ m₁ n₂ m₂ ≤₁ ≤₂ | no ¬p with k + n₁ <? m₂
... | yes q = ⊥-elim $ ¬p $ +-cancelʳ-≤ (suc k) m₁ (≤-trans q ≤₂)
... | no  _ = cong var (+-assoc k _ _)
↑[]↑[] (func f) n₁ m₁ n₂ m₂ ≤₁ ≤₂ = refl
↑[]↑[] (app t₁ t₂) n₁ m₁ n₂ m₂ ≤₁ ≤₂
  rewrite ↑[]↑[] t₁ n₁ m₁ n₂ m₂ ≤₁ ≤₂
        | ↑[]↑[] t₂ n₁ m₁ n₂ m₂ ≤₁ ≤₂ = refl

↑↑[] : ∀ {l} (t : Termₙ l) (n₁ n₂ m₂ : ℕ) → m₂ ≤ n₁
  → (t ↑ n₁) ↑[ m₂ ] n₂ ≡ t ↑ (n₁ + n₂)
↑↑[] t n₁ n₂ m₂ ≤ = ↑[]↑[] t n₁ 0 n₂ m₂ z≤n ≤

↑↑ : ∀ {l} (t : Termₙ l) (n₁ n₂ : ℕ) → (t ↑ n₁) ↑ n₂ ≡ t ↑ (n₁ + n₂)
↑↑ t n₁ n₂ = ↑↑[] t n₁ n₂ 0 z≤n
