---
title: Agda一阶逻辑(2) 定义
zhihu-tags: Agda, 数理逻辑
---

# Agda一阶逻辑(2) 定义

> 交流Q群: 893531731  
> 本文源码: [Definition.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/FOL/Definition.lagda.md)  
> 高亮渲染: [Definition.html](https://choukh.github.io/agda-flypitch/FOL.Definition.html)  

## 前言

本篇引入一阶逻辑的核心定义, 而性质的证明则放在后篇. 如上一篇所说, 本篇的所有内容都是参数化到签名之上的.

```agda
{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Signature
open Signature

module FOL.Definition {u} (σ : Signature {u}) where
```

### 标准库依赖

```agda
open import Level renaming (suc to lsuc)
open import Data.Bool using (if_then_else_)
open import Data.Nat using (ℕ; suc; _≤ᵇ_; _<ᵇ_; _+_; _∸_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Unary using (Pred; _∈_; _⊆_)
open import Function using (_$_)
open import StdlibExt.Relation.Unary
```

### 符号优先级

```agda
infix 100 ~_
infix 10 _↑[_]_ _↑_ _↥[_]_ _↥_ _[_/_]
infix 9 _≈_
infix 8 _⇔_
infix 7 _⇒_
infixr 6 _∧_
infixr 5 _∨_
infix 4 _⊢_
```

## 项

粗略类比, 如果说符号相当于字, 那么**项 (term)** 和**公式 (formula)** 则相当于词和句. 更准确地说, 项由变量与函数符号构成; 公式则由关系符号, 等号, 量化符号与连接符号等构成.

与签名的处理类似地，我们把函数的元数编码进项的类型里：变量和常量是 **0-项**，n元函数是 **n-项**。此外，变量采用 [De Brujin编码](https://en.wikipedia.org/wiki/De_Bruijn_index)，即把任意自然数当作变量。

**定义 (项)** 归纳定义 n-项:

- 对任意自然数 `n`，变量 `var n` 是 `0`-项.
- 对任意 `l` 元函数符号 `f`，函数 `func f` 是 `l`-项.
- 对任意 `suc l`-项 `t₁` 和任意 `0`-项 `t₂`，函数应用 `app t₁ t₂` 是 `l`-项.

特别地，`0`-项简称项。

```agda
data Termₙ : ℕ → Set u where
  var  : ∀ (n : ℕ) → Termₙ 0
  func : ∀ {l} (f : σ .functions l) → Termₙ l
  app  : ∀ {l} (t₁ : Termₙ (suc l)) (t₂ : Termₙ 0) → Termₙ l

Term = Termₙ 0
```

## 公式

n元关系在公式中的处理与n元函数在项中的处理类似, 我们把关系的元数编码进公式的类型里: n元关系是 **n-公式**.

至此, 非逻辑符号处理完毕. 接下来处理[逻辑符号](https://zh.wikipedia.org/wiki/%E4%B8%80%E9%98%B6%E9%80%BB%E8%BE%91#%E9%82%8F%E8%BC%AF%E7%AC%A6%E8%99%9F). 它们通常包括:

1. 等号: = (≈)
2. 量化符号:
  - 全称量化: ∀ (∀')
  - 存在量化: ∃ (∃')
3. 连接符号:
  - 否定: ¬ (~)
  - 蕴含: → (⇒)
  - 等价: ↔ (⇔)
  - 且: ∧
  - 或: ∨

括号中是为了避免与Agda元语言符号冲突而在本文中使用的符号.

这些符号不是独立的, 只需选取其中一些作为原始符号, 剩下的可以由它们推导出来. 不同的书根据不同的理由做出了不同的选取, 但得到的一阶逻辑系统基本是一样的. 我们根据Agda形式化的简便性 (具体会在后文逐渐体现), 选取等号 ≈, 蕴含 ⇒ , 全称量化 ∀' 和恒假 ⊥ 作为原始符号.

**定义 (公式)** 归纳定义 n-公式:

- 恒假 `⊥` 是 `0`-公式.
- 对任意 `l` 元关系符号 `r`，关系 `rel r` 是 `l`-公式.
- 对任意 `suc l`-公式 `φ` 和任意项 `t`，关系应用 `appᵣ φ t` 是 `l`-公式.
- 对任意项 `t₁` 和 `t₂`，等式 `t₁ ≈ t₂` 是 `0`-公式.
- 对任意 `0`-公式 `φ₁` 和任意 `0`-公式 `φ₂`，蕴含式 `φ₁ ⇒ φ₂` 是 `0`-公式.
- 对任意 `0`-公式 `φ`，全称量化式 `∀' φ` 是 `0`-公式.

特别地, `0`-公式简称公式.

```agda
data Formulaₙ : ℕ → Set u where
  ⊥     : Formulaₙ 0
  rel   : ∀ {l} (r : σ .relations l) → Formulaₙ l
  appᵣ  : ∀ {l} (φ : Formulaₙ (suc l)) (t : Term) → Formulaₙ l
  _≈_   : ∀ (t₁ t₂ : Term) → Formulaₙ 0
  _⇒_   : ∀ (φ₁ φ₂ : Formulaₙ 0) → Formulaₙ 0
  ∀'_   : ∀ (φ : Formulaₙ 0) → Formulaₙ 0

Formula = Formulaₙ 0
```

**注意** 我们将元数编码进类型里是为了省去所谓的[合式公式 (well-formed formula，WFF)](https://zh.wikipedia.org/wiki/%E5%90%88%E5%BC%8F%E5%85%AC%E5%BC%8F) 谓词. 任意 `φ : Formula` 都是合式公式, 类型正确性保证了 `φ` 的合式性.


## 导出符号

仿照类型论的处理, φ 的否定定义为 φ 蕴含恒假. 而恒真则是恒假的否定. 由于我们的对象逻辑是经典逻辑, 所以可以这样方便地处理.

```agda
~_ : Formula → Formula
~ φ = φ ⇒ ⊥

⊤ : Formula
⊤ = ~ ⊥
```

其他逻辑符号的定义也是同样地利用了经典逻辑的特性. 它们都可以在加了排中律的 Agda 中"证"出来.

```agda
_∧_ : Formula → Formula → Formula
φ₁ ∧ φ₂ = ~ (φ₁ ⇒ ~ φ₂)

_∨_ : Formula → Formula → Formula
φ₁ ∨ φ₂ = ~ φ₁ ⇒ φ₂

_⇔_ : Formula → Formula → Formula
φ₁ ⇔ φ₂ = φ₁ ⇒ φ₂ ∧ φ₂ ⇒ φ₁

∃'_ : Formula → Formula
∃' φ = ~ (∀' ~ φ)
```

## 变量提升

```agda
_↑[_]_ : ∀ {l} (t : Termₙ l) (m n : ℕ) → Termₙ l
var k     ↑[ m ] n = if m ≤ᵇ k then var (k + n) else var k
func f    ↑[ m ] n = func f
app t₁ t₂ ↑[ m ] n = app (t₁ ↑[ m ] n) (t₂ ↑[ m ] n)

_↑_ : ∀ {l} (t : Termₙ l) (n : ℕ) → Termₙ l
t ↑ n = t ↑[ 0 ] n

_↥[_]_ : ∀ {l} (φ : Formulaₙ l) (m n : ℕ) → Formulaₙ l
⊥         ↥[ m ] n = ⊥
rel R     ↥[ m ] n = rel R
appᵣ φ t  ↥[ m ] n = appᵣ (φ ↥[ m ] n) (t ↑[ m ] n)
(t₁ ≈ t₂) ↥[ m ] n = t₁ ↑[ m ] n ≈ t₂ ↑[ m ] n
(φ₁ ⇒ φ₂) ↥[ m ] n = φ₁ ↥[ m ] n ⇒ φ₂ ↥[ m ] n
∀' φ      ↥[ m ] n = ∀' (φ ↥[ suc m ] n)

_↥_ : ∀ {l} (φ : Formulaₙ l) (n : ℕ) → Formulaₙ l
φ ↥ n = φ ↥[ 0 ] n
```

## 变量替换

```agda
-- t₁ t₂ t₃ t₄ t₅ t₆ t₇ ...
-- t₁ t₂ t₃ s  t₄ t₅ t₆ ...
insert_into_at_ : ∀ {u} {T : Set u} (s : T) (v : ℕ → T) (n : ℕ) → (ℕ → T)
(insert s into v at n) k = if k <ᵇ n then v k else if n <ᵇ k then v (k ∸ 1) else s

[_/ᵥ_] : ∀ (s : Term) (n : ℕ) → (ℕ → Term)
[ s /ᵥ n ] = insert (s ↑ n) into var at n

_[_/ₜ_] : ∀ {l} (t : Termₙ l) (s : Term) (n : ℕ) → Termₙ l
var k     [ s /ₜ n ] = [ s /ᵥ n ] k
func f    [ s /ₜ n ] = func f
app t₁ t₂ [ s /ₜ n ] = app (t₁ [ s /ₜ n ]) (t₂ [ s /ₜ n ])

_[_/_] : ∀ {l} (φ : Formulaₙ l) (s : Term) (n : ℕ) → Formulaₙ l
⊥         [ s / n ] = ⊥
rel R     [ s / n ] = rel R
appᵣ φ t  [ s / n ] = appᵣ (φ [ s / n ]) (t [ s /ₜ n ])
(t₁ ≈ t₂) [ s / n ] = t₁ [ s /ₜ n ] ≈ t₂ [ s /ₜ n ]
(φ₁ ⇒ φ₂) [ s / n ] = φ₁ [ s / n ] ⇒ φ₂ [ s / n ]
∀' φ      [ s / n ] = ∀' (φ [ s / suc n ])
```

## 证明

```agda
Theory = Pred (Formula) u

_⇑_ : Theory → ℕ → Theory
Γ ⇑ n = (_↥ 1) ⟦ Γ ⟧
```

```agda
data _⊢_ : Theory → Formula → Set (lsuc u) where
  axiom     : ∀ {Γ φ} → φ ∈ Γ → Γ ⊢ φ
  ⊥-elim    : ∀ {Γ φ} → Γ ⨭ ~ φ ⊢ ⊥ → Γ ⊢ φ
  ≈-refl    : ∀ Γ t → Γ ⊢ t ≈ t
  ⇒-intro   : ∀ {Γ φ₁ φ₂} → Γ ⨭ φ₁ ⊢ φ₂ → Γ ⊢ φ₁ ⇒ φ₂
  ⇒-elim    : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ⇒ φ₂ → Γ ⊢ φ₁ → Γ ⊢ φ₂
  ∀-intro   : ∀ {Γ φ} → Γ ⇑ 1 ⊢ φ → Γ ⊢ ∀' φ
  ∀-elim    : ∀ {Γ φ t} → Γ ⊢ ∀' φ → Γ ⊢ φ [ t / 0 ]
  subst     : ∀ {Γ s t φ} → Γ ⊢ s ≈ t → Γ ⊢ φ [ s / 0 ] → Γ ⊢ φ [ t / 0 ]
```

## 理论的弱化

```agda
weakening : ∀ {Γ Δ} {φ} → Γ ⊆ Δ → Γ ⊢ φ → Δ ⊢ φ
weakening Γ⊆Δ (axiom φ∈Γ)     = axiom   (Γ⊆Δ φ∈Γ)
weakening Γ⊆Δ (⊥-elim ⊢)      = ⊥-elim  (weakening (⨭⊆⨭ Γ⊆Δ) ⊢)
weakening Γ⊆Δ (≈-refl _ t)    = ≈-refl _ t
weakening Γ⊆Δ (⇒-intro ⊢)     = ⇒-intro (weakening (⨭⊆⨭ Γ⊆Δ) ⊢)
weakening Γ⊆Δ (⇒-elim ⊢₁ ⊢₂)  = ⇒-elim  (weakening Γ⊆Δ ⊢₁) (weakening Γ⊆Δ ⊢₂)
weakening Γ⊆Δ (∀-intro ⊢)     = ∀-intro (weakening (⟦⟧⊆⟦⟧ Γ⊆Δ) ⊢)
weakening Γ⊆Δ (∀-elim ⊢)      = ∀-elim  (weakening Γ⊆Δ ⊢)
weakening Γ⊆Δ (subst ⊢₁ ⊢₂)   = subst   (weakening Γ⊆Δ ⊢₁) (weakening Γ⊆Δ ⊢₂)

weakening1 : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₂ → Γ ⨭ φ₁ ⊢ φ₂
weakening1 = weakening ⊆⨭

weakening2 : ∀ {Γ φ₁ φ₂ φ₃} → Γ ⨭ φ₁ ⊢ φ₂ → Γ ⨭ φ₃ ⨭ φ₁ ⊢ φ₂
weakening2 = weakening (⨭⊆⨭ ⊆⨭)
```

```agda
axiom1 : ∀ {Γ : Theory} {φ} → Γ ⨭ φ ⊢ φ
axiom1 = axiom (inj₂ refl)

axiom2 : ∀ {Γ : Theory} {φ₁ φ₂} → Γ ⨭ φ₁ ⨭ φ₂ ⊢ φ₁
axiom2 = axiom (inj₁ (inj₂ refl))

-- deduction
⇒-elim-axiom : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ⇒ φ₂ → Γ ⨭ φ₁ ⊢ φ₂
⇒-elim-axiom Γ⊢⇒ = ⇒-elim (weakening1 Γ⊢⇒) axiom1

⇒-intro-tauto : ∀ {φ₁ φ₂} → (∀ {Γ} → Γ ⊢ φ₁ → Γ ⊢ φ₂) → ∀ {Δ} → Δ ⊢ φ₁ ⇒ φ₂
⇒-intro-tauto ⊢ = ⇒-intro (weakening inj₂ (⊢ (axiom refl)))
```

## 导出规则

```agda
exfalso : ∀ {Γ φ} → Γ ⊢ ⊥ → Γ ⊢ φ
exfalso Γ⊢⊥ = ⊥-elim (weakening1 Γ⊢⊥)

tauto-exfalso : ∀ {Γ φ} → Γ ⊢ ⊥ ⇒ φ
tauto-exfalso = ⇒-intro-tauto exfalso
```

```agda
∧-intro : ∀ {Γ} {φ₁ φ₂ : Formula} → Γ ⊢ φ₁ → Γ ⊢ φ₂ → Γ ⊢ φ₁ ∧ φ₂
∧-intro Γ⊢φ₁ Γ⊢φ₂ = ⇒-intro $ ⇒-elim (⇒-elim axiom1 (weakening1 Γ⊢φ₁)) (weakening1 Γ⊢φ₂)

∧-elimₗ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ∧ φ₂ → Γ ⊢ φ₁
∧-elimₗ ⊢∧ = ⊥-elim $ ⇒-elim (weakening1 ⊢∧) (⇒-intro $ exfalso $ ⇒-elim axiom2 axiom1)

∧-elimᵣ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ∧ φ₂ → Γ ⊢ φ₂
∧-elimᵣ ⊢∧ = ⊥-elim $ ⇒-elim (weakening1 ⊢∧) (⇒-intro axiom2)

∨-introₗ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ → Γ ⊢ φ₁ ∨ φ₂
∨-introₗ Γ⊢φ₁ = ⇒-intro $ exfalso $ ⇒-elim axiom1 (weakening1 Γ⊢φ₁)

∨-introᵣ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₂ → Γ ⊢ φ₁ ∨ φ₂
∨-introᵣ Γ⊢φ₂ = ⇒-intro $ weakening1 Γ⊢φ₂

∨-elim : ∀ {Γ φ₁ φ₂ φ₃} → Γ ⊢ φ₁ ∨ φ₂ → Γ ⨭ φ₁ ⊢ φ₃ → Γ ⨭ φ₂ ⊢ φ₃ → Γ ⊢ φ₃
∨-elim Γ⊢∨ ⊢₁ ⊢₂ = ⊥-elim $ ⇒-elim axiom1 Γ⨭φ₃⇒⊥⊢φ₃ where
  Γ⨭φ₃⇒⊥⊢φ₃ = ⇒-elim (⇒-intro $ weakening2 ⊢₂) Γ⨭φ₃⇒⊥⊢φ₂ where
    Γ⨭φ₃⇒⊥⊢φ₂ = ⇒-elim (weakening1 Γ⊢∨) (⇒-intro $ ⇒-elim axiom2 (weakening2 ⊢₁))
```

```agda
no-contra : ∀ {Γ φ} → Γ ⊢ φ ∧ ~ φ → Γ ⊢ ⊥
no-contra ⊢ = ⇒-elim (∧-elimᵣ ⊢) (∧-elimₗ ⊢)

tauto-no-contra : ∀ {Γ φ} → Γ ⊢ ~ (φ ∧ ~ φ)
tauto-no-contra = ⇒-intro-tauto no-contra
```

```agda
⇔-intro : ∀ {Γ φ₁ φ₂} → Γ ⨭ φ₁ ⊢ φ₂ → Γ ⨭ φ₂ ⊢ φ₁ → Γ ⊢ φ₁ ⇔ φ₂
⇔-intro ⊢₁ ⊢₂ = ∧-intro (⇒-intro ⊢₁) (⇒-intro ⊢₂)

⇔-elimₗ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ⇔ φ₂ → Γ ⨭ φ₁ ⊢ φ₂
⇔-elimₗ ⊢⇔ = ⇒-elim-axiom (∧-elimₗ ⊢⇔)

⇔-elimᵣ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ⇔ φ₂ → Γ ⨭ φ₂ ⊢ φ₁
⇔-elimᵣ ⊢⇔ = ⇒-elim-axiom (∧-elimᵣ ⊢⇔)

⇔-refl : ∀ {Γ φ} → Γ ⊢ φ → Γ ⊢ φ ⇔ φ
⇔-refl ⊢ = ⇔-intro axiom1 axiom1

⇔-sym : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ⇔ φ₂ → Γ ⊢ φ₂ ⇔ φ₁
⇔-sym ⊢ = ⇔-intro (⇔-elimᵣ ⊢) (⇔-elimₗ ⊢)

⇒-trans : ∀ {Γ φ₁ φ₂ φ₃} → Γ ⊢ φ₁ ⇒ φ₂ → Γ ⊢ φ₂ ⇒ φ₃ → Γ ⊢ φ₁ ⇒ φ₃
⇒-trans ⊢₁ ⊢₂ = ⇒-intro $ ⇒-elim (weakening1 ⊢₂) (⇒-elim (weakening1 ⊢₁) axiom1)

⇔-trans : ∀ {Γ φ₁ φ₂ φ₃} → Γ ⊢ φ₁ ⇔ φ₂ → Γ ⊢ φ₂ ⇔ φ₃ → Γ ⊢ φ₁ ⇔ φ₃
⇔-trans ⊢₁ ⊢₂ = ∧-intro
  (⇒-trans (∧-elimₗ ⊢₁) (∧-elimₗ ⊢₂))
  (⇒-trans (∧-elimᵣ ⊢₂) (∧-elimᵣ ⊢₁))
```

```agda
∃-intro : ∀ {Γ φ} (t : Term) → Γ ⊢ φ [ t / 0 ] → Γ ⊢ ∃' φ
∃-intro t ⊢ = ⇒-intro $ ⇒-elim (∀-elim axiom1) (weakening1 ⊢)

∃-elim : ∀ {Γ φ₁ φ₂} → Γ ⊢ ∃' φ₁ → Γ ⇑ 1 ⨭ φ₁ ⊢ φ₂ ↥ 1 → Γ ⊢ φ₂
∃-elim ⊢∃ ⊢ = ⊥-elim $ ⇒-elim
  (weakening1 ⊢∃)
  (∀-intro $ ⇒-intro $ ⇒-elim
    (weakening1 $ weakening ⊆⟦⨭⟧ axiom1)
    (weakening (⨭⊆⨭ $ ⟦⟧⊆⟦⟧ ⊆⨭) ⊢)
  )
```