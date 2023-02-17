{-# OPTIONS --cubical-compatible --safe #-}

open import FOL.Signature
module FOL.Lemmas.Substitution {u} (σ : Signature {u}) where
open import FOL.Base (σ) hiding (⊥-elim; subst)

open import Data.Nat
open import Data.Empty using (⊥-elim)
open import Function using (_$_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; sym; trans; subst)
open import StdlibExt.Data.Nat.Properties

[/]ᵥ-cong : ∀ {u} {T : Set u} {𝓋 𝓊 : ℕ → T} (ext : ∀ n → 𝓋 n ≡ 𝓊 n) (s : T) (n k : ℕ)
  → (𝓋 [ s / n ]ᵥ) k ≡ (𝓊 [ s / n ]ᵥ) k
[/]ᵥ-cong ext s n k with <-cmp k n
... | tri< _ _ _ = ext k
... | tri≈ _ _ _ = refl
... | tri> _ _ _ = ext (k ∸ 1)

[/][/]ᵥ : ∀ {u} {T : Set u} (𝓋 : ℕ → T) (s₁ s₂ : T) (n₁ n₂ k : ℕ)
  → (𝓋 [ s₂ / n₁ + n₂ ]ᵥ [ s₁ / n₁ ]ᵥ) k ≡ (𝓋 [ s₁ / n₁ ]ᵥ [ s₂ / n₁ + n₂ + 1 ]ᵥ) k
[/][/]ᵥ 𝓋 s₁ s₂ n₁ n₂ k with <-cmp k n₁ | <-cmp k (n₁ + n₂ + 1)
... | tri< _ _ ¬p   | tri≈ _ refl _ = ⊥-elim $ ¬p $ m<m+n+1 _ _
... | tri≈ _ refl _ | tri≈ ¬p _ _   = ⊥-elim $ ¬p $ m<m+n+1 _ _
... | tri≈ _ refl _ | tri> ¬p _ _   = ⊥-elim $ ¬p $ m<m+n+1 _ _
... | tri< p _ _    | tri> ¬q _ _   = ⊥-elim $ ¬q $ ≤-trans p $ ≤-trans (n≤1+n _) (m<m+n+1 _ _)
[/][/]ᵥ 𝓋 s₁ s₂ n₁ n₂ k | tri≈ _ refl _ | tri< _ _ _ with <-cmp k n₁
... | tri≈ _ _ _  = refl
... | tri< _ ¬p _ = ⊥-elim $ ¬p refl
... | tri> _ ¬p _ = ⊥-elim $ ¬p refl
[/][/]ᵥ 𝓋 s₁ s₂ n₁ n₂ k | tri> _ _ _    | tri≈ _ refl _ with <-cmp (k ∸ 1) (n₁ + n₂)
... | tri≈ _ _ _  = refl
... | tri< _ ¬p _ = ⊥-elim $ ¬p $ m+n∸n≡m (n₁ + n₂) 1
... | tri> _ ¬p _ = ⊥-elim $ ¬p $ m+n∸n≡m (n₁ + n₂) 1
[/][/]ᵥ 𝓋 s₁ s₂ n₁ n₂ k | tri< p ¬q _   | tri< _ _ _ with <-cmp k n₁ | <-cmp k (n₁ + n₂)
... | tri< _ _ _    | tri< _ _ _    = refl
... | tri≈ _ refl _ | _             = ⊥-elim $ ¬q $ refl
... | tri> ¬p _ _   | _             = ⊥-elim $ ¬p p
... | _             | tri≈ ¬q _ _   = ⊥-elim $ ¬q (≤-trans p (m≤m+n _ _))
... | _             | tri> ¬q _ _   = ⊥-elim $ ¬q (≤-trans p (m≤m+n _ _))
[/][/]ᵥ 𝓋 s₁ s₂ n₁ n₂ k | tri> _ ¬p q   | tri< r _ _ with <-cmp k n₁ | <-cmp (k ∸ 1) (n₁ + n₂)
... | tri> _ _ _    | tri< _ _ _    = refl
... | tri< _ _ ¬q   | _             = ⊥-elim $ ¬q q
... | tri≈ _ refl _ | _             = ⊥-elim $ ¬p $ refl
... | _             | tri≈ ¬s _ _   = ⊥-elim $ ¬s $ +-cancelʳ-< _ _ $ subst (_< _) (sym $ m∸n+n≡m $ ≤-trans (s≤s z≤n) q) r
... | _             | tri> ¬s _ _   = ⊥-elim $ ¬s $ +-cancelʳ-< _ _ $ subst (_< _) (sym $ m∸n+n≡m $ ≤-trans (s≤s z≤n) q) r
[/][/]ᵥ 𝓋 s₁ s₂ n₁ n₂ k | tri> _ _ p    | tri> ¬q ¬r _ with <-cmp (k ∸ 1) (n₁ + n₂) | <-cmp (k ∸ 1) n₁
... | tri> _ _ _    | tri> _ _ _    = refl
... | tri> _ _ s    | tri< _ _ ¬t   = ⊥-elim $ ¬t $ ≤-trans (s≤s $ m≤m+n _ _) s
... | tri< s _ _    | _             = ⊥-elim $ ¬q $ subst (suc k ≤_) (sym $ +-comm _ 1) (s≤s $ subst (_≤ _) 1+k∸1≡k s) where
  1+k∸1≡k = trans (+-comm 1 _) (m∸n+n≡m $ ≤-trans (s≤s z≤n) p)
... | tri≈ _ s _    | _             rewrite sym s = ⊥-elim $ ¬r (sym (m∸n+n≡m (≤-trans (s≤s z≤n) p)))
... | tri> ¬s ¬t _  | tri≈ _ u _    with n₂
... | zero   rewrite +-identityʳ n₁ = ⊥-elim $ ¬t $ u
... | suc n₂ rewrite u              = ⊥-elim $ ¬s (m<m+n n₁ (s≤s z≤n))
