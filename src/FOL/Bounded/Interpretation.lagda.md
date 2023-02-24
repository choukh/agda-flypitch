---
title: Agda一阶逻辑(5) 束缚项解释
zhihu-tags: Agda, 数理逻辑
---

# Agda一阶逻辑(5) 束缚项解释

> 交流Q群: 893531731  
> 本文源码: [Interpretation.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/FOL/Bounded/Interpretation.lagda.md)  
> 高亮渲染: [Interpretation.html](https://choukh.github.io/agda-flypitch/FOL.Bounded.Interpretation.html)  

## 前言

```agda
{-# OPTIONS --cubical-compatible --safe #-}

open import FOL.Signature
module FOL.Bounded.Interpretation (ℒ : Signature {u}) where
open import FOL.Bounded.Base ℒ
open import FOL.Interpretation ℒ using (Interpretation) public
```

### 标准库依赖

```agda
open import Level
open import Data.Empty using (⊥-elim)
open import Data.Empty.Polymorphic renaming (⊥ to False) hiding (⊥-elim)
open import Data.Product using (Σ-syntax)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Unit.Polymorphic using (tt)
open import Function using (_$_)
open import Relation.Nullary using (Dec)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary.PropositionalEquality using (_≡_)
```

## 实现

```agda
module PreRealizer (𝒮 : Interpretation) where
  open Interpretation 𝒮
  open Termₗ
  open Formulaₗ

  realizeₜ : ∀ (𝓋 : Vec Domain n) (t : Termₗ n l) (xs : Vec Domain l) → Domain
  realizeₜ 𝓋 (var k)      xs = lookup 𝓋 k
  realizeₜ 𝓋 (func f)     xs = funmap f xs
  realizeₜ 𝓋 (app t₁ t₂)  xs = realizeₜ 𝓋 t₁ ((realizeₜ 𝓋 t₂ []) ∷ xs)

  realize : ∀ (𝓋 : Vec Domain n) (φ : Formulaₗ n l) (xs : Vec Domain l) → Set u
  realize 𝓋 ⊥          xs = False
  realize 𝓋 (rel R)    xs = relmap R xs
  realize 𝓋 (appᵣ φ t) xs = realize 𝓋 φ (realizeₜ 𝓋 t [] ∷ xs)
  realize 𝓋 (t₁ ≈ t₂)  xs = realizeₜ 𝓋 t₁ xs ≡ realizeₜ 𝓋 t₂ xs
  realize 𝓋 (φ₁ ⇒ φ₂)  xs = realize 𝓋 φ₁ xs → realize 𝓋 φ₂ xs
  realize 𝓋 (∀' φ)     xs = ∀ x → realize (x ∷ 𝓋) φ xs
```

```agda
open Interpretation
module OpenedRealizer (𝒮 : Interpretation) {n} (𝓋 : Vec (Domain 𝒮) n) where
  open PreRealizer 𝒮 renaming (realizeₜ to rₜ; realize to r)

  realizeₜ : Term n → Domain 𝒮
  realizeₜ t = rₜ 𝓋 t []

  realize : Formula n → Set u
  realize φ = r 𝓋 φ []
```

```agda
module ClosedRealizer (𝒮 : Interpretation) where
  open OpenedRealizer 𝒮 [] public
```

## 可满足性

```agda
open ClosedRealizer
infix 4 _⊨ˢ_ _⊨ᵀ_ _⊨_

_⊨ˢ_ : Interpretation → Sentence → Set u
𝒮 ⊨ˢ φ = realize 𝒮 φ

_⊨ᵀ_ : Interpretation → Theory → Set u
𝒮 ⊨ᵀ Γ = ∀ φ → φ ∈ Γ → 𝒮 ⊨ˢ φ

_⊨_ : Theory → Sentence → Set (suc u)
Γ ⊨ φ = ∀ 𝒮 → Domain 𝒮 → 𝒮 ⊨ᵀ Γ → 𝒮 ⊨ˢ φ
```
