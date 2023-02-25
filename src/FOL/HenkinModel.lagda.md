---
title: Agda一阶逻辑(?) Henkin构造
zhihu-tags: Agda, 数理逻辑
zhihu-url: https://zhuanlan.zhihu.com/p/604316612
---

# Agda一阶逻辑(?) Henkin构造

> 交流Q群: 893531731  
> 本文源码: [HenkinModel.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/FOL/HenkinModel.lagda.md)  
> 高亮渲染: [HenkinModel.html](https://choukh.github.io/agda-flypitch/FOL.HenkinModel.html)  

```agda
{-# OPTIONS --cubical-compatible --safe #-}

module FOL.HenkinModel {u} where

open import FOL.Signature hiding (u) renaming (Signature to Language)
open import FOL.Bounded.Base
open import FOL.Signature.Homomorphism using (_⟶_)
open Language {u}
```

```agda
open import Data.Nat using (ℕ)
open import Function using (_$_; id)
```

```agda
data Functions ℒ : ℕ → Set u where
  including  : ∀ {n} → ℒ .functions n → Functions ℒ n
  witnessing : Formula ℒ 1 → Functions ℒ 0
```

```agda
stepᴸ : Language → Language
stepᴸ ℒ = record { functions = Functions ℒ ; relations = ℒ .relations }
```

```agda
witness : Formula ℒ 1 → Constants $ stepᴸ ℒ
witness = Functions.witnessing
```

```agda
morph : ℒ ⟶ stepᴸ ℒ
morph = record { funhomo = Functions.including ; relhomo = id }
```

```agda
--[witness] : Formula ℒ 1 → Constants ℒ → Sentence ℒ
--[witness] φ c = {! (∃' φ) ⇒ φ [ const c / 0 ]  !}
```
