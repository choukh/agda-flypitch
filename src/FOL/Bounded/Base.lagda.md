---
title: Agda一阶逻辑(5) 束缚
zhihu-tags: Agda, 数理逻辑
---

# Agda一阶逻辑(5) 束缚

> 交流Q群: 893531731  
> 本文源码: [Base.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/FOL/Bounded/Base.lagda.md)  
> 高亮渲染: [Base.html](https://choukh.github.io/agda-flypitch/FOL.Bounded.Base.html)  

## 前言

```agda
{-# OPTIONS --cubical-compatible --safe #-}

open import FOL.Signature using (Signature)
open Signature

module FOL.Bounded.Base {u} (σ : Signature {u}) where
import FOL.Base σ as Free
open Free using (var; func; app; var-injective; app-injectiveˡ; app-injectiveʳ)
```

### 标准库依赖

```agda
open import Level renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc; _<?_; _+_; _∸_)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ-injective)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import StdlibExt.Relation.Unary
```

### 符号优先级

```agda
infix 100 ~_
infix 9 _≈_
infix 8 _⇔_
infix 7 _⇒_
infixr 6 _∧_
infixr 5 _∨_
infix 4 _⊢_
```

## 束缚项

```agda
data Termₗ (n : ℕ) : ℕ → Set u where
  var  : ∀ (k : Fin n) → Termₗ n 0
  func : ∀ {l} (f : σ .functions l) → Termₗ n l
  app  : ∀ {l} (t₁ : Termₗ n (suc l)) (t₂ : Termₗ n 0) → Termₗ n l

Term = λ n → Termₗ n 0
```

### 闭项

```agda
ClosedTermₗ = λ l → Termₗ 0 l

ClosedTerm = ClosedTermₗ 0
```

## 束缚公式

```agda
data Formulaₗ (n : ℕ) : ℕ → Set u where
  ⊥     : Formulaₗ n 0
  rel   : ∀ {l} (r : σ .relations l) → Formulaₗ n l
  appᵣ  : ∀ {l} (φ : Formulaₗ n (suc l)) (t : Term n) → Formulaₗ n l
  _≈_   : ∀ (t₁ t₂ : Term n) → Formulaₗ n 0
  _⇒_   : ∀ (φ₁ φ₂ : Formulaₗ n 0) → Formulaₗ n 0
  ∀'_   : ∀ (φ : Formulaₗ (suc n) 0) → Formulaₗ n 0

Formula = λ n → Formulaₗ n 0
```

### 句子 (闭公式)

```agda
Sentenceₗ = λ l → Formulaₗ 0 l
Sentence = Sentenceₗ 0
```

### 理论

```agda
Theory = Pred (Sentence) u
```

### 导出符号

```agda
~_ : ∀ {n} → Formula n → Formula n
~ φ = φ ⇒ ⊥

⊤ : Sentence
⊤ = ~ ⊥

_∧_ : ∀ {n} → Formula n → Formula n → Formula n
φ₁ ∧ φ₂ = ~ (φ₁ ⇒ ~ φ₂)

_∨_ : ∀ {n} → Formula n → Formula n → Formula n
φ₁ ∨ φ₂ = ~ φ₁ ⇒ φ₂

_⇔_ : ∀ {n} → Formula n → Formula n → Formula n
φ₁ ⇔ φ₂ = φ₁ ⇒ φ₂ ∧ φ₂ ⇒ φ₁

∃'_ : ∀ {n} → Formula (suc n) → Formula n
∃' φ = ~ (∀' ~ φ)
```

## 解束缚

```agda
unboundₜ : ∀ {n l} → Termₗ n l → Free.Termₗ l
unboundₜ (var k)     = var $ toℕ k
unboundₜ (func f)    = func f
unboundₜ (app t₁ t₂) = app (unboundₜ t₁) (unboundₜ t₂)
```

```agda
unbound : ∀ {n l} → Formulaₗ n l → Free.Formulaₗ l
unbound φ = {!   !}
```

## 证明

```agda
_⊢_ : Theory → Sentence → Set (lsuc u)
Γ ⊢ φ = unbound ⟦ Γ ⟧ Free.⊢ unbound φ
```
