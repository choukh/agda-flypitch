---
title: Agda一阶逻辑(?) Henkin模型
zhihu-tags: Agda, 数理逻辑
---

# Agda一阶逻辑(?) Henkin模型

> 交流Q群: 893531731  
> 本文源码: [HenkinModel.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/FOL/HenkinModel.lagda.md)  
> 高亮渲染: [HenkinModel.html](https://choukh.github.io/agda-flypitch/FOL.HenkinModel.html)  

```agda
{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --lossy-unification #-}

module FOL.HenkinModel {u} where

open import FOL.Language hiding (u)
open import FOL.Bounded.Base using (Formula; Sentence; Theory)
open import FOL.Language.Diagram using (Diagram)
import FOL.Language.Homomorphism as LHom
import FOL.Bounded.Substitution
open Language {u}
open LHom using (_⟶_; _∘_) renaming (id to idᴸ)
```

```agda
open import Data.Nat
open import Data.Nat.Properties
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_$_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import StdlibExt.Relation.Unary using (_∪_; _⟦_⟧; replacement-syntax)
open import Tools.DirectedDiagram using (ℕᴰ)
```

```agda
data Functions ℒ : ℕ → Set u where
  include  : ∀ {n} → ℒ .functions n → Functions ℒ n
  witness : Formula ℒ 1 → Functions ℒ 0
```

```agda
languageStep : Language → Language
languageStep ℒ = record { functions = Functions ℒ ; relations = ℒ .relations }
```

```agda
languageMorph : ℒ ⟶ languageStep ℒ
languageMorph = record { funcMorph = Functions.include ; relMorph = id }
```

```agda
languageChainObject : Language → ℕ → Language
languageChainObject ℒ zero    = ℒ
languageChainObject ℒ (suc n) = languageStep (languageChainObject ℒ n)
```

```agda
languageChainMorph : ∀ {x y} → x ≤ y → languageChainObject ℒ x ⟶ languageChainObject ℒ y
languageChainMorph {ℒ} {x} {y} x≤y with m≤n⇒m<n∨m≡n x≤y
... | inj₁ (s≤s x≤y-1) = languageMorph ∘ languageChainMorph x≤y-1
... | inj₂ refl = idᴸ
```

```agda
fuck : ∀ {x y} → (f₁ : x ≤ y) → (f₂ : x ≤ y) → languageChainMorph f₁ ≡ languageChainMorph f₂
fuck f₁ f₂ = {! refl  !}
```

```agda
languageChainFunctorial : ∀ {x y z : ℕ} {f₁ : x ≤ y} {f₂ : y ≤ z} {f₃ : x ≤ z}
  → languageChainMorph {ℒ} f₃ ≡ (languageChainMorph f₂ ∘ languageChainMorph f₁)
languageChainFunctorial {ℒ} {x} {y} {z} {x≤y} {y≤z} {x≤z} with m≤n⇒m<n∨m≡n x≤y | m≤n⇒m<n∨m≡n y≤z | m≤n⇒m<n∨m≡n x≤z
... | inj₁ x<x  | inj₂ refl | inj₂ refl = ⊥-elim (<-irrefl refl x<x)
... | inj₂ refl | inj₁ x<x  | inj₂ refl = ⊥-elim (<-irrefl refl x<x)
... | inj₂ refl | inj₂ refl | inj₁ x<x  = ⊥-elim (<-irrefl refl x<x)
... | inj₁ x<y  | inj₁ y<x  | inj₂ refl = ⊥-elim (<-asym x<y y<x)
... | inj₁ (s≤s x≤y-1) | inj₁ (s≤s y≤z-1) | inj₁ (s≤s x≤z-1) = {!   !} --cong (languageMorph ∘_) {!   !}
--languageChainFunctorial {f₁ = x≤y} {f₂ = y≤z-1} {f₃ = x≤z-1}
--languageChainFunctorial {f₁ = x≤y-1} {f₂ = ?} {f₃ = x≤y}
... | inj₂ refl | inj₁ x<z  | inj₁ _    = {!   !}
... | inj₁ x<y  | inj₂ refl | inj₁ _    = {!   !}
... | inj₂ refl | inj₂ refl | inj₂ fuck = {!   !}
```

```agda
languageChain : Language → Diagram ℕᴰ
languageChain ℒ = record
  { obj         = languageChainObject ℒ
  ; morph       = languageChainMorph
  ; functorial  = languageChainFunctorial
  }
```

```agda
witnessOf : Formula ℒ 1 → Constant $ languageStep ℒ
witnessOf = Functions.witness
```

```agda
[_witnessing_] : Constant ℒ → Formula ℒ 1 → Sentence ℒ
[_witnessing_] {ℒ} c φ = (∃' φ) ⇒ φ [ const c / 0 ] where
  open FOL.Bounded.Base ℒ
  open FOL.Bounded.Substitution ℒ
```

```agda
theoryStep : Theory ℒ → Theory $ languageStep ℒ
theoryStep {ℒ} Γ = theoryMorph Γ ∪ ｛ [ witnessOf φ witnessing formulaMorph φ ] ∣ φ ∈ Formula ℒ 1 ｝
  where open LHom.Bounded languageMorph
```
 