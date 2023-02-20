---
title: Agda一阶逻辑(4) 可靠性
zhihu-tags: Agda, 数理逻辑
---

# Agda一阶逻辑(4) 可靠性

> 交流Q群: 893531731  
> 本文源码: [Soundness.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/FOL/Properties/Soundness.lagda.md)  
> 高亮渲染: [Soundness.html](https://choukh.github.io/agda-flypitch/FOL.Properties.Soundness.html)  

```agda
{-# OPTIONS --cubical-compatible --safe #-}

open import FOL.Signature
module FOL.Properties.Soundness {u} (σ : Signature {u}) where
open import FOL.Base (σ)
open import FOL.Interpretation (σ)
open import FOL.Lemmas.Realization (σ)
open Interpretation
open Realizer

open import Level using (lift)
open import Data.Nat using (ℕ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary.PropositionalEquality using (refl)
open import StdlibExt.Relation.Nullary
open import StdlibExt.Relation.Binary.PropositionalEquivalence u hiding (_∘_)
```

```agda
soundness : ∀ {Γ φ} → Γ ⊢ φ → Γ ⊨ φ
soundness (axiom φ∈Γ) 𝒾 𝓋 v = v _ φ∈Γ
soundness {Γ} {φ} (⊥-elim ⊢₀) 𝒾 𝓋 v = byContra (dec 𝒾 𝓋 φ) λ ¬ → soundness ⊢₀ 𝒾 𝓋
  λ { φ₁ (inj₁ φ∈Γ)  → v φ₁ φ∈Γ
    ; φ₁ (inj₂ refl) → lift ∘ ¬ }
soundness (≈-refl _ t) 𝒾 𝓋 v = refl
soundness (⇒-intro ⊢₀) 𝒾 𝓋 v r = soundness ⊢₀ 𝒾 𝓋
  λ { φ (inj₁ φ∈Γ)  → v φ φ∈Γ
    ; φ (inj₂ refl) → r }
soundness (⇒-elim ⊢₁ ⊢₂) 𝒾 𝓋 v = (soundness ⊢₁ 𝒾 𝓋 v) (soundness ⊢₂ 𝒾 𝓋 v)
soundness (∀-intro ⊢₀) 𝒾 𝓋 v x = soundness ⊢₀ 𝒾 _
  λ { φ (ψ , ψ∈Γ , refl) → from (realize-subst-lift 𝒾 𝓋 0 ψ x) ⟨$⟩ v ψ ψ∈Γ}
soundness (∀-elim a) 𝒾 𝓋 v = {!   !}
soundness (subst a a₁) 𝒾 𝓋 v = {!   !}
```
