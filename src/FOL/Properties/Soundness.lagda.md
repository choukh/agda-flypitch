---
title: Agda一阶逻辑(6) 可靠性
zhihu-tags: Agda, 数理逻辑
---

# Agda一阶逻辑(6) 可靠性

> 交流Q群: 893531731  
> 本文源码: [Soundness.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/FOL/Properties/Soundness.lagda.md)  
> 高亮渲染: [Soundness.html](https://choukh.github.io/agda-flypitch/FOL.Properties.Soundness.html)  

```agda
{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Signature
module FOL.Properties.Soundness (ℒ : Signature {u}) where

open import Level using (lift)
open import Data.Nat using (ℕ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_; _$_)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary.PropositionalEquality using (refl; sym)
open import StdlibExt.Relation.Nullary
open import StdlibExt.Relation.Binary.PropositionalEquivalence u hiding (_∘_; sym)
```

```agda
module Free where
  open import FOL.Base ℒ
  open import FOL.Interpretation ℒ
  open import FOL.Lemmas.Realization ℒ
  open Realizer

  soundness : ∀ {Γ φ} → Γ ⊢ φ → Γ ⊨ φ
  soundness (axiom φ∈Γ) _ _ 𝒮⊨Γ = 𝒮⊨Γ _ φ∈Γ
  soundness {_} {φ} (⊥-elim ⊢₀) 𝒮 𝓋 𝒮⊨Γ = byContra λ ¬ → soundness ⊢₀ 𝒮 𝓋
    λ { φ₁ (inj₁ φ∈Γ)  → 𝒮⊨Γ φ₁ φ∈Γ
      ; φ₁ (inj₂ refl) → lift ∘ ¬ }
  soundness (≈-refl _ t) _ _ _ = refl
  soundness (⇒-intro ⊢₀) 𝒮 𝓋 𝒮⊨Γ r = soundness ⊢₀ 𝒮 𝓋
    λ { φ (inj₁ φ∈Γ)  → 𝒮⊨Γ φ φ∈Γ
      ; φ (inj₂ refl) → r }
  soundness (⇒-elim ⊢₁ ⊢₂) 𝒮 𝓋 𝒮⊨Γ = (soundness ⊢₁ 𝒮 𝓋 𝒮⊨Γ) (soundness ⊢₂ 𝒮 𝓋 𝒮⊨Γ)
  soundness (∀-intro ⊢₀) 𝒮 𝓋 𝒮⊨Γ x = soundness ⊢₀ 𝒮 _
    λ { φ (ψ , ψ∈Γ , refl) → from (realize-subst-lift 𝒮 𝓋 0 ψ x) ⟨$⟩ 𝒮⊨Γ ψ ψ∈Γ }
  soundness (∀-elim {_} {φ} {t} ⊢₀) 𝒮 𝓋 𝒮⊨Γ = to (realize-subst0 𝒮 𝓋 φ t) ⟨$⟩ soundness ⊢₀ 𝒮 𝓋 𝒮⊨Γ _
  soundness (subst {_} {s} {t} {φ} ⊢₁ ⊢₂) 𝒮 𝓋 𝒮⊨Γ = to (realize-subst0 𝒮 𝓋 φ t) ⟨$⟩ H where
    H : realize 𝒮 (𝓋 [ realizeₜ 𝒮 𝓋 t / 0 ]ᵥ) φ
    H rewrite sym $ soundness ⊢₁ 𝒮 𝓋 𝒮⊨Γ = from (realize-subst0 𝒮 𝓋 φ s) ⟨$⟩ (soundness ⊢₂ 𝒮 𝓋 𝒮⊨Γ)
```

```agda
open import FOL.Bounded.Base ℒ using (_⊢_)
open import FOL.Bounded.Interpretation ℒ using (_⊨_)
open import FOL.Bounded.Lemmas.Satisfiability ℒ using (bound⊨)

soundness : ∀ {Γ φ} → Γ ⊢ φ → Γ ⊨ φ
soundness = bound⊨ ∘ Free.soundness
```
