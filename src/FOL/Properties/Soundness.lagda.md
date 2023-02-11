---
title: Agda一阶逻辑(4) 可靠性
zhihu-tags: Agda, 数理逻辑
---

# Agda一阶逻辑(4) 可靠性

> 交流Q群: 893531731  
> 本文源码: [Soundness.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/FOL/Properties/Soundness.lagda.md)  
> 高亮渲染: [Soundness.html](https://choukh.github.io/agda-flypitch/FOL.Properties.Soundness.html)  

```agda
open import FOL.Signature
module FOL.Properties.Soundness {u} (σ : Signature {u}) where
open import FOL.Base (σ)
open import FOL.Realization (σ)
open import FOL.Lemmas.Realization (σ)

open import Level using (lift)
open import Data.Nat using (ℕ)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality.Core using (refl)
open import StdlibExt.Classical using (byContra)
```

```agda
postulate
  dec : ∀ 𝒾 φ → Dec (realize 𝒾 φ)

soundness : ∀ {Γ φ} → Γ ⊢ φ → Γ ⊨ φ
soundness (axiom φ∈Γ) 𝒾 v = v _ φ∈Γ
soundness {Γ} {φ} (⊥-elim ⊢⊥) 𝒾 v = byContra (dec 𝒾 φ) λ ¬ → soundness ⊢⊥ 𝒾
  λ { φ₁ (inj₁ φ∈Γ)  → v φ₁ φ∈Γ
    ; φ₁ (inj₂ refl) → lift ∘ ¬ }
soundness (≈-refl _ t)    𝒾 v = refl
soundness (⇒-intro ⊢₂)    𝒾 v r = soundness ⊢₂ 𝒾
  λ { φ (inj₁ φ∈Γ)  → v φ φ∈Γ
    ; φ (inj₂ refl) → r }
soundness (⇒-elim ⊢₁ ⊢₂)  𝒾 v = (soundness ⊢₁ 𝒾 v) (soundness ⊢₂ 𝒾 v)
soundness (∀-intro ⊢)     𝒾 v = {!   !}
soundness (∀-elim ⊢)      𝒾 v = {!   !}
soundness (subst ⊢₁ ⊢₂)   𝒾 v = {!   !}
```
