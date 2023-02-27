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

module FOL.HenkinModel {u} where

open import Level
open import FOL.Language hiding (u)
open import FOL.Bounded.Base using (Formula; Sentence; Theory)
open import FOL.Language.Diagram using (Diagram)
import FOL.Language.Homomorphism as LHom
import FOL.Bounded.Substitution
open Language {u}
open LHom using (_⟶_)
```

```agda
open import Data.Nat using (ℕ; zero; suc)
open import Function using (_$_; id)
open import StdlibExt.Relation.Unary using (_∪_; _⟦_⟧; replacement-syntax)
open import Tools.DirectedDiagram using (ℕᴰ)
```

```agda
data Functions ℒ : ℕ → Set u where
  include  : ∀ {n} → ℒ .functions n → Functions ℒ n
  witness : Formula ℒ 1 → Functions ℒ 0
```

```agda
Stepᴸ : Language → Language
Stepᴸ ℒ = record { functions = Functions ℒ ; relations = ℒ .relations }
```

```agda
languageMorph : ℒ ⟶ Stepᴸ ℒ
languageMorph = record { funcMorph = Functions.include ; relMorph = id }
```

```agda
witnessOf : Formula ℒ 1 → Constant $ Stepᴸ ℒ
witnessOf = Functions.witness
```

```agda
[_witnessing_] : Constant ℒ → Formula ℒ 1 → Sentence ℒ
[_witnessing_] {ℒ} c φ = (∃' φ) ⇒ φ [ const c / 0 ] where
  open FOL.Bounded.Base ℒ
  open FOL.Bounded.Substitution ℒ
```

```agda
Step : Theory ℒ → Theory $ Stepᴸ ℒ
Step {ℒ} Γ = theoryMorph Γ ∪ ｛ [ witnessOf φ witnessing formulaMorph φ ] ∣ φ ∈ Formula ℒ 1 ｝
  where open LHom.Bounded languageMorph
```

```agda
chainᴸ : Language → ℕ → Language
chainᴸ ℒ zero    = ℒ
chainᴸ ℒ (suc n) = Stepᴸ (chainᴸ ℒ n)
```

```agda
chainDiagram : Language → Diagram ℕᴰ
chainDiagram ℒ = record
  { obj = chainᴸ ℒ
  ; morph = {!   !}
  ; functorial = {!   !}
  }
```
