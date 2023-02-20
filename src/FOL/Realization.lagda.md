---
title: Agda一阶逻辑(3) 解释
zhihu-tags: Agda, 数理逻辑
---

# Agda一阶逻辑(3) 解释

> 交流Q群: 893531731  
> 本文源码: [Realization.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/FOL/Realization.lagda.md)  
> 高亮渲染: [Realization.html](https://choukh.github.io/agda-flypitch/FOL.Realization.html)  

## 前言

```agda
{-# OPTIONS --cubical-compatible --safe #-}

open import FOL.Signature
module FOL.Realization {u} (σ : Signature {u}) where
open import FOL.Base (σ)
open Signature
```

### 标准库依赖

```agda
open import Level using (suc)
open import Data.Empty.Polymorphic renaming (⊥ to False)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary.PropositionalEquality using (_≡_)
```

## 解释 (结构)

函数符号和关系符号的一套实际所指就构成了一阶逻辑的一种解释 (从解释所得到的实际产物的角度来看又叫做结构). 它由一个集合 `domain` 以及两个映射 `funmap` 和 `relmap` 组成. 其中 `funmap` 用于映射函数符号到函数, `relmap` 用于映射关系符号到关系. 注意函数和关系的n元参数编码为n维向量.

```agda
record Interpretation : Set (suc u) where
  field
    domain : Set u
    funmap : ∀ {n} → σ .functions n → Vec domain n → domain
    relmap : ∀ {n} → σ .relations n → Vec domain n → Set u

open Interpretation

Valuation : Interpretation → Set u
Valuation 𝒾 = ℕ → 𝒾 .domain
```

## 实现

```agda
module PreRealization (𝒾 : Interpretation) where
  open Termₙ
  open Formulaₙ

  realizeₜ : ∀ {l} (𝓋 : Valuation 𝒾) (t : Termₙ l) (xs : Vec (𝒾 .domain) l) → 𝒾 .domain
  realizeₜ 𝓋 (var k)     xs = 𝓋 k
  realizeₜ 𝓋 (func f)    xs = 𝒾 .funmap f xs
  realizeₜ 𝓋 (app t₁ t₂) xs = realizeₜ 𝓋 t₁ ((realizeₜ 𝓋 t₂ []) ∷ xs)

  realize : ∀ {l} (𝓋 : Valuation 𝒾) (φ : Formulaₙ l) (xs : Vec (𝒾 .domain) l) → Set u
  realize 𝓋 ⊥          xs = False
  realize 𝓋 (rel r)    xs = 𝒾 .relmap r xs
  realize 𝓋 (appᵣ φ t) xs = realize 𝓋 φ (realizeₜ 𝓋 t [] ∷ xs)
  realize 𝓋 (t₁ ≈ t₂)  xs = realizeₜ 𝓋 t₁ xs ≡ realizeₜ 𝓋 t₂ xs
  realize 𝓋 (φ₁ ⇒ φ₂)  xs = realize 𝓋 φ₁ xs → realize 𝓋 φ₂ xs
  realize 𝓋 (∀' φ)     xs = ∀ x → realize (𝓋 [ x / 0 ]ᵥ) φ xs
```

```agda
module _ (𝒾 : Interpretation) (𝓋 : Valuation 𝒾) where
  open PreRealization 𝒾 renaming (realizeₜ to rₜ; realize to r)

  realizeₜ : Term → 𝒾 .domain
  realizeₜ t = rₜ 𝓋 t []

  realize : Formula → Set u
  realize φ = r 𝓋 φ []

  valid : Theory → Set u
  valid Γ = ∀ φ → φ ∈ Γ → realize φ
```

## 可满足性

```agda
_⊨_ : Theory → Formula → Set (suc u)
Γ ⊨ φ = ∀ 𝒾 𝓋 → valid 𝒾 𝓋 Γ → realize 𝒾 𝓋 φ
```
