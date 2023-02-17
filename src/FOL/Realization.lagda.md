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
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
```

## 结构

函数符号和关系符号的实际所指所组成的资料叫做结构. 它由一个集合 `carrier` (也可以叫做论域) 以及两个映射 `funmap` 和 `relmap` 组成. 其中 `funmap` 用于映射函数符号到元函数, `relmap` 用于映射关系符号到元关系. 注意函数和关系的n元参数编码为n维向量.

```agda
record Structure {u} (σ : Signature {u}) : Set (suc u) where
  field
    carrier : Set u
    funmap : ∀ {n} → σ .functions n → Vec carrier n → carrier
    relmap : ∀ {n} → σ .relations n → Vec carrier n → Set u

open Structure
```

## 解释

```agda
module PreRealization (𝒮 : Structure σ) where
  open Termₙ
  open Formulaₙ

  realizeₜ : ∀ {l} (𝓋 : ℕ → 𝒮 .carrier) (t : Termₙ l) (xs : Vec (𝒮 .carrier) l) → 𝒮 .carrier
  realizeₜ 𝓋 (var k)     xs = 𝓋 k
  realizeₜ 𝓋 (func f)    xs = 𝒮 .funmap f xs
  realizeₜ 𝓋 (app t₁ t₂) xs = realizeₜ 𝓋 t₁ ((realizeₜ 𝓋 t₂ []) ∷ xs)

  realize : ∀ {l} (𝓋 : ℕ → 𝒮 .carrier) (φ : Formulaₙ l) (xs : Vec (𝒮 .carrier) l) → Set u
  realize 𝓋 ⊥          xs = False
  realize 𝓋 (rel r)    xs = 𝒮 .relmap r xs
  realize 𝓋 (appᵣ φ t) xs = realize 𝓋 φ (realizeₜ 𝓋 t [] ∷ xs)
  realize 𝓋 (t₁ ≈ t₂)  xs = realizeₜ 𝓋 t₁ xs ≡ realizeₜ 𝓋 t₂ xs
  realize 𝓋 (φ₁ ⇒ φ₂)  xs = realize 𝓋 φ₁ xs → realize 𝓋 φ₂ xs
  realize 𝓋 (∀' φ)     xs = ∀ x → realize (𝓋 [ x / 0 ]ᵥ) φ xs
```

```agda
record Interpretation : Set (suc u) where
  field
    structure : Structure σ
    valuation : ℕ → structure .carrier
```

```agda
module _ (𝒾 : Interpretation) where
  open Interpretation

  realizeₜ : ∀ (t : Term) → 𝒾 .structure .carrier
  realizeₜ t = PreRealization.realizeₜ (𝒾 .structure) (𝒾 .valuation) t []

  realize : ∀ (φ : Formula) → Set u
  realize φ = PreRealization.realize (𝒾 .structure) (𝒾 .valuation) φ []
```

## 可满足性

```agda
valid : Interpretation → Theory → Set u
valid 𝒾 Γ = ∀ φ → φ ∈ Γ → realize 𝒾 φ

_⊨_ : Theory → Formula → Set (suc u)
Γ ⊨ φ = ∀ 𝒾 → valid 𝒾 Γ → realize 𝒾 φ
```
