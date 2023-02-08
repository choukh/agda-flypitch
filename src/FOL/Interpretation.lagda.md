---
title: Agda一阶逻辑(3) 解释
zhihu-tags: Agda, 数理逻辑
---

# Agda一阶逻辑(3) 解释

> 交流Q群: 893531731  
> 本文源码: [Interpretation.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/FOL/Interpretation.lagda.md)  
> 高亮渲染: [Interpretation.html](https://choukh.github.io/agda-flypitch/FOL.Interpretation.html)  

## 前言

```agda
{-# OPTIONS --cubical-compatible --safe #-}

open import FOL.Dependency
open Structure

module FOL.Interpretation {u} {σ : Signature {u}} (𝒮 : Structure {u} {σ}) where
```

### 标准库依赖

```agda
open import Level renaming (suc to lsuc)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_)
open import Function using (_$_)

open import FOL.Base (σ) using (Termₙ)
open Termₙ
```

```agda
module _ (v : ℕ → 𝒮 .carrier) where

  interpreteₜ : ∀ {l} (t : Termₙ l) (x : Vec (𝒮 .carrier) l) → 𝒮 .carrier
  interpreteₜ (var k)    x = v k
  interpreteₜ (func f)   x = 𝒮 .funmap f x
  interpreteₜ (app t₁ t₂) x = interpreteₜ t₁ $ interpreteₜ t₂ [] ∷ x
```
