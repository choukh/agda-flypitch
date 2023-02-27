---
title: Agda一阶逻辑(4) 自由项解释
zhihu-tags: Agda, 数理逻辑
---

# Agda一阶逻辑(4) 自由项解释

> 交流Q群: 893531731  
> 本文源码: [Interpretation.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/FOL/Interpretation.lagda.md)  
> 高亮渲染: [Interpretation.html](https://choukh.github.io/agda-flypitch/FOL.Interpretation.html)  

## 前言

```agda
{-# OPTIONS --cubical-compatible --safe #-}

open import FOL.Language
module FOL.Interpretation (ℒ : Language {u}) where
open import FOL.Base ℒ hiding (⊥-elim)
open Language ℒ
```

### 标准库依赖

```agda
open import Level
open import Axiom.ExcludedMiddle
open import Data.Empty using (⊥-elim)
open import Data.Empty.Polymorphic renaming (⊥ to False) hiding (⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Unit.Polymorphic using (tt)
open import Function using (_$_)
open import Relation.Nullary using (Dec)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)
```

## 解释 (结构)

函数符号和关系符号的一套实际所指就构成了一阶逻辑的一种解释 (从解释所得到的实际产物的角度来看又叫做结构). 它由一个集合 `Domain` 以及两个映射 `funmap` 和 `relmap` 组成. 其中 `funmap` 用于映射函数符号到函数, `relmap` 用于映射关系符号到关系. 注意函数和关系的n元参数编码为n维向量.

此外, 由于一阶逻辑是经典逻辑, 其解释也必须是经典的, 因此还需要经典逻辑的排中律 `classical`. 我们把它标记为实例参数 (instance arguments) 使得它用起来就像一个局部的公理.

```agda
record Interpretation : Set (suc u) where
  field
    Domain : Set u
    funmap : ∀ {n} → functions n → Vec Domain n → Domain
    relmap : ∀ {n} → relations n → Vec Domain n → Set u
    ⦃ classical ⦄ : ExcludedMiddle u
```

## 实现

```agda
module PreRealizer (𝒮 : Interpretation) where
  open Interpretation 𝒮
  open Termₗ
  open Formulaₗ

  realizeₜ : ∀ (𝓋 : ℕ → Domain) (t : Termₗ l) (xs : Vec Domain l) → Domain
  realizeₜ 𝓋 (var k)     xs = 𝓋 k
  realizeₜ 𝓋 (func f)    xs = funmap f xs
  realizeₜ 𝓋 (app t₁ t₂) xs = realizeₜ 𝓋 t₁ ((realizeₜ 𝓋 t₂ []) ∷ xs)

  realize : ∀ (𝓋 : ℕ → Domain) (φ : Formulaₗ l) (xs : Vec Domain l) → Set u
  realize 𝓋 ⊥          xs = False
  realize 𝓋 (rel R)    xs = relmap R xs
  realize 𝓋 (appᵣ φ t) xs = realize 𝓋 φ (realizeₜ 𝓋 t [] ∷ xs)
  realize 𝓋 (t₁ ≈ t₂)  xs = realizeₜ 𝓋 t₁ xs ≡ realizeₜ 𝓋 t₂ xs
  realize 𝓋 (φ₁ ⇒ φ₂)  xs = realize 𝓋 φ₁ xs → realize 𝓋 φ₂ xs
  realize 𝓋 (∀' φ)     xs = ∀ x → realize (𝓋 [ x / 0 ]ᵥ) φ xs
```

```agda
open Interpretation
module Realizer (𝒮 : Interpretation) (𝓋 : ℕ → Domain 𝒮) where
  open PreRealizer 𝒮 renaming (realizeₜ to rₜ; realize to r)

  realizeₜ : Term → Domain 𝒮
  realizeₜ t = rₜ 𝓋 t []

  realize : Formula → Set u
  realize φ = r 𝓋 φ []
```

## 可满足性

```agda
open Realizer
infix 4 _⊨[_]_ _⊨_

_⊨[_]_ : ∀ (𝒮 : Interpretation) (𝓋 : ℕ → Domain 𝒮) → Theory → Set u
𝒮 ⊨[ 𝓋 ] Γ = ∀ φ → φ ∈ Γ → realize 𝒮 𝓋 φ

_⊨_ : Theory → Formula → Set (suc u)
Γ ⊨ φ = ∀ 𝒮 𝓋 → 𝒮 ⊨[ 𝓋 ] Γ → realize 𝒮 𝓋 φ
```
