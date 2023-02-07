---
title: Agda一阶逻辑(2) 定义
zhihu-tags: Agda, 数理逻辑
zhihu-url: https://zhuanlan.zhihu.com/p/604316612
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
open import Data.Nat using (ℕ; suc; _<ᵇ_; _+_; _∸_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Unary using (Pred; _∈_; _⊆_)
open import StdlibExt.Relation.Unary renaming (_⨭_ to _,_; ⨭⊆⨭ to ,⊆,; ⊆⨭ to ⊆,; ⊆⟦⨭⟧ to ⊆⟦,⟧)
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

变量提升属于[De Brujin编码](https://en.wikipedia.org/wiki/De_Bruijn_index)方案的一部分, 用于处理量词的绑定, 具体会在后文中体现.

简单来说, 变量提升就是把变量符号表 `var : ℕ → Term` 的某一段去掉, 以剩下的变量符号来重新表达原来的项和公式. 例如, 对项 `t`, 从 `var m` 开始, 去掉 `n` 个符号, 就叫做将 `t` 从 `m` 提升 `n`, 记作 `t ↑[ m ] n`.

如果项 `t` 使用了变量 `var 0`, `var 1`, `var 2`, `var 3`, 那么 `t ↑[ 1 ] 2` 则会使用变量 `var 0`, `var 3`, `var 4`, `var 5`.

特别地, 如果 `m = 0`, 就叫做将 `t` 提升 `n`, 记作 `t ↑ n`.

```agda
_↑[_]_ : ∀ {l} (t : Termₙ l) (m n : ℕ) → Termₙ l
var k     ↑[ m ] n = if k <ᵇ m then var k else var (k + n)
func f    ↑[ m ] n = func f
app t₁ t₂ ↑[ m ] n = app (t₁ ↑[ m ] n) (t₂ ↑[ m ] n)

_↑_ : ∀ {l} (t : Termₙ l) (n : ℕ) → Termₙ l
t ↑ n = t ↑[ 0 ] n
```

对公式的变量提升基本上就是对其中的项进行变量提升, 或者是对公式中的公式递归地提升. 只是对于量词构造的公式, 保留一位变量不提升, 以作为量词的绑定变量.

```agda
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

变量替换用于处理量词绑定变量的替换和等量的替换. 首先我们需要一个帮助函数, 往序列 `v : ℕ → T` 中插入指定的项 `s` 于指定的位置 `n`. 例如, 如果 `v` 是序列

`t₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ ...`

那么 `insert s into v at 4` 就是序列

`t₀ t₁ t₂ t₃ s t₄ t₅ t₆ t₇ ...`

```agda
insert_into_at_ : ∀ {u} {T : Set u} (s : T) (v : ℕ → T) (n : ℕ) → (ℕ → T)
(insert s into v at n) k = if k <ᵇ n then v k else if n <ᵇ k then v (k ∸ 1) else s
```

将项 `t` 中的变量 `var n` (如果存在) 替换为项 `s` 后得到的项记作 `t [ s /ₜ n ]`. 如果项是变量 `var k`, 那么将变量符号表 `var` 改造成 `insert (s ↑ n) into var at n`, 再取其中的第 `k` 个. 如果项是函数应用, 那么递归地替换其中的项.

其中, `insert (s ↑ n) into var at n` 的意思是往 `var` 中插入 `s ↑ n` 于 `n` 处. 将 `s` 提升 `n` 是为了保证 `s` 中的变量不会与 `t` 中的变量冲突.

```agda
_[_/ₜ_] : ∀ {l} (t : Termₙ l) (s : Term) (n : ℕ) → Termₙ l
var k     [ s /ₜ n ] = insert (s ↑ n) into var at n $ k
func f    [ s /ₜ n ] = func f
app t₁ t₂ [ s /ₜ n ] = app (t₁ [ s /ₜ n ]) (t₂ [ s /ₜ n ])
```

对公式的变量替换基本上就是对其中的项进行变量替换, 或者是对公式中的公式递归地替换. 只是对于量词构造的公式, 将替换的位置顺延一位, 因为首位是量词的绑定变量.

```agda
_[_/_] : ∀ {l} (φ : Formulaₙ l) (s : Term) (n : ℕ) → Formulaₙ l
⊥         [ s / n ] = ⊥
rel R     [ s / n ] = rel R
appᵣ φ t  [ s / n ] = appᵣ (φ [ s / n ]) (t [ s /ₜ n ])
(t₁ ≈ t₂) [ s / n ] = t₁ [ s /ₜ n ] ≈ t₂ [ s /ₜ n ]
(φ₁ ⇒ φ₂) [ s / n ] = φ₁ [ s / n ] ⇒ φ₂ [ s / n ]
∀' φ      [ s / n ] = ∀' (φ [ s / suc n ])
```

## 理论

公式的集合叫做**理论 (theory)**. 如有违和感, 那么可能是因为这种定义是对朴素意义的理论的一种过度一般化, 这时只需认为理论就是"公式的集合"的别名即可.

```agda
Theory = Pred (Formula) u
```

理论 `Γ` 在函数 `_↥ n` 之下的像叫做理论 `Γ` 的 `n` 提升, 记作 `Γ ⇑ n`.

```agda
_⇑_ : Theory → ℕ → Theory
Γ ⇑ n = (_↥ n) ⟦ Γ ⟧
```

## 证明

有了以上概念的准备, 我们终于可以定义何为证明. 我们采用所谓[**自然演绎 (natural deduction)**](https://zh.m.wikipedia.org/zh/%E8%87%AA%E7%84%B6%E6%BC%94%E7%BB%8E)的方案.

**定义 (证明)** 我们说理论 `Γ` 可以证明公式 `φ` (记作 `Γ ⊢ φ`) 当且仅当以下任意一种情况成立:

- `φ` 是理论 `Γ` 的公理, 即 `φ ∈ Γ`.
- `Γ` 加上 `~ φ` 可以证明假. **("假"的引出规则)**
- `φ` 是某项 `t` 构造的等式 `t ≈ t`. **(等式的引出规则)**
- `φ` 是某公式 `φ₁` 和 `φ₂` 构造的蕴含式 `φ₁ ⇒ φ₂`, 且 `Γ` 加上 `φ₁` 可以证明 `φ₂`. **(蕴含式的引入规则)**
- 已知 `Γ` 可以证明 `φ₁ ⇒ φ`, 且 `Γ` 可以证明 `φ₁`. **(蕴含式的引出规则)**
- `φ` 是某公式 `φ₁` 构造的全称量化式 `∀' φ₁`, 且 `Γ ⇑ 1` 可以证明 `φ₁`. **(全称量化式的引入规则)**
- `φ` 是将某公式 `φ₁` 的变量 `var 0` 替换成某项 `t` 而得到的公式 `φ₁ [ t / 0 ]`, 且 `Γ` 可以证明 `∀' φ₁`. **(全称量化式的引出规则)**
- `φ` 是某替换式 `φ₁ [ t / 0 ]`, 且 `Γ` 可以证明 `φ₁ [ s / 0 ]`, 且 `Γ` 可以证明 `t` 和 `s` 相等. **(替换规则)**

```agda
data _⊢_ : Theory → Formula → Set (lsuc u) where
  axiom     : ∀ {Γ φ} → φ ∈ Γ → Γ ⊢ φ
  ⊥-elim    : ∀ {Γ φ} → Γ , ~ φ ⊢ ⊥ → Γ ⊢ φ
  ≈-refl    : ∀ Γ t → Γ ⊢ t ≈ t
  ⇒-intro   : ∀ {Γ φ₁ φ₂} → Γ , φ₁ ⊢ φ₂ → Γ ⊢ φ₁ ⇒ φ₂
  ⇒-elim    : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ⇒ φ₂ → Γ ⊢ φ₁ → Γ ⊢ φ₂
  ∀-intro   : ∀ {Γ φ} → Γ ⇑ 1 ⊢ φ → Γ ⊢ ∀' φ
  ∀-elim    : ∀ {Γ φ t} → Γ ⊢ ∀' φ → Γ ⊢ φ [ t / 0 ]
  subst     : ∀ {Γ s t φ} → Γ ⊢ s ≈ t → Γ ⊢ φ [ s / 0 ] → Γ ⊢ φ [ t / 0 ]
```

以上规则大部分都符合直观, 我们只讲全称量词相关的两条规则 `∀-intro` 和 `∀-elim`. 首先这两条可以合并看作一条: `Γ ⇑ 1 ⊢ φ → Γ ⊢ φ [ t / 0 ]`. 它说如果不使用变量 `var 0` 而表达的理论 `Γ ⇑ 1` 能证明 `φ`, 那么可以将 `φ` 中的 `var 0` 换成任意项, 所得到的 `φ [ t / 0 ]` 能被恢复使用 `var 0` 的理论 `Γ` 所证明. 这就是从指定 `var 0` 为全称量化专用变量, 到将它替换为其他项并撤销该指定的自然过程, 而 `∀' φ` 只是这一过程的中间状态表示.

## 理论的弱化

我们将补完导出符号 `∧` 等的相关规则. 为此需要先证明一个重要引理.

**引理 (弱化)** 对于任意理论 `Γ` 和 `Δ`, 如果 `Δ` 包含了 `Γ`, 那么 `Γ` 可以证明的任意 `φ` 都可以被 `Δ` 证明.

证明: 简单的集合论事实配合归纳法即可. ∎

```agda
weakening : ∀ {Γ Δ} {φ} → Γ ⊆ Δ → Γ ⊢ φ → Δ ⊢ φ
weakening Γ⊆Δ (axiom φ∈Γ)     = axiom   (Γ⊆Δ φ∈Γ)
weakening Γ⊆Δ (⊥-elim ⊢)      = ⊥-elim  (weakening (,⊆, Γ⊆Δ) ⊢)
weakening Γ⊆Δ (≈-refl _ t)    = ≈-refl _ t
weakening Γ⊆Δ (⇒-intro ⊢)     = ⇒-intro (weakening (,⊆, Γ⊆Δ) ⊢)
weakening Γ⊆Δ (⇒-elim ⊢₁ ⊢₂)  = ⇒-elim  (weakening Γ⊆Δ ⊢₁) (weakening Γ⊆Δ ⊢₂)
weakening Γ⊆Δ (∀-intro ⊢)     = ∀-intro (weakening (⟦⟧⊆⟦⟧ Γ⊆Δ) ⊢)
weakening Γ⊆Δ (∀-elim ⊢)      = ∀-elim  (weakening Γ⊆Δ ⊢)
weakening Γ⊆Δ (subst ⊢₁ ⊢₂)   = subst   (weakening Γ⊆Δ ⊢₁) (weakening Γ⊆Δ ⊢₂)
```

以下是两个简单的变化形式, 它们会经常用到.

```agda
weakening1 : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₂ → Γ , φ₁ ⊢ φ₂
weakening1 = weakening ⊆,

weakening2 : ∀ {Γ φ₁ φ₂ φ₃} → Γ , φ₁ ⊢ φ₂ → Γ , φ₃ , φ₁ ⊢ φ₂
weakening2 = weakening (,⊆, ⊆,)
```

与之类似地是 `axiom` 规则的两个变化形式.

```agda
axiom1 : ∀ {Γ : Theory} {φ} → Γ , φ ⊢ φ
axiom1 = axiom (inj₂ refl)

axiom2 : ∀ {Γ : Theory} {φ₁ φ₂} → Γ , φ₁ , φ₂ ⊢ φ₁
axiom2 = axiom (inj₁ (inj₂ refl))
```

## 导出规则

### `⇒` 的补充规则

`⇒-intro` 在有些书中称为[**演绎定理 (deduction theorem)**](https://zh.wikipedia.org/wiki/%E4%B8%80%E9%98%B6%E9%80%BB%E8%BE%91#%E6%BC%94%E7%B9%B9%E5%85%83%E5%AE%9A%E7%90%86). 我们这里直接指定为规则. 以下是它的逆命题. 两者结合表明了 `Γ , φ₁ ⊢ φ₂` 与 `Γ ⊢ φ₁ ⇒ φ₂` 的等价性.

```agda
⇒-elim-to-axiom : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ⇒ φ₂ → Γ , φ₁ ⊢ φ₂
⇒-elim-to-axiom Γ⊢⇒ = ⇒-elim (weakening1 Γ⊢⇒) axiom1
```

以下可以认为是 `⇒-elim` 的逆命题, 但要注意 `→` 的两边都要对理论做全称量化. 此外, 满足 `∀ Γ → Γ ⊢ φ` 的 `φ` 又称为**恒真式 (tautology)**. 所以以下命题又称为恒真式的引入规则.

```agda
⇒-intro-tauto : ∀ {φ₁ φ₂} → (∀ {Γ} → Γ ⊢ φ₁ → Γ ⊢ φ₂) → ∀ {Δ} → Δ ⊢ φ₁ ⇒ φ₂
⇒-intro-tauto ⊢ = ⇒-intro (weakening inj₂ (⊢ (axiom refl)))
```

以下规则我们直接列出名称而不再加以说明.

### 归谬法

```agda
exfalso : ∀ {Γ φ} → Γ ⊢ ⊥ → Γ ⊢ φ
exfalso Γ⊢⊥ = ⊥-elim (weakening1 Γ⊢⊥)

tauto-exfalso : ∀ {Γ φ} → Γ ⊢ ⊥ ⇒ φ
tauto-exfalso = ⇒-intro-tauto exfalso
```

### `∧` 的引入引出规则

```agda
∧-intro : ∀ {Γ} {φ₁ φ₂ : Formula} → Γ ⊢ φ₁ → Γ ⊢ φ₂ → Γ ⊢ φ₁ ∧ φ₂
∧-intro Γ⊢φ₁ Γ⊢φ₂ = ⇒-intro $ ⇒-elim (⇒-elim axiom1 (weakening1 Γ⊢φ₁)) (weakening1 Γ⊢φ₂)

∧-elimₗ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ∧ φ₂ → Γ ⊢ φ₁
∧-elimₗ ⊢∧ = ⊥-elim $ ⇒-elim (weakening1 ⊢∧) (⇒-intro $ exfalso $ ⇒-elim axiom2 axiom1)

∧-elimᵣ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ∧ φ₂ → Γ ⊢ φ₂
∧-elimᵣ ⊢∧ = ⊥-elim $ ⇒-elim (weakening1 ⊢∧) (⇒-intro axiom2)
```

### `∨` 的引入引出规则

```agda
∨-introₗ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ → Γ ⊢ φ₁ ∨ φ₂
∨-introₗ Γ⊢φ₁ = ⇒-intro $ exfalso $ ⇒-elim axiom1 (weakening1 Γ⊢φ₁)

∨-introᵣ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₂ → Γ ⊢ φ₁ ∨ φ₂
∨-introᵣ Γ⊢φ₂ = ⇒-intro $ weakening1 Γ⊢φ₂

∨-elim : ∀ {Γ φ₁ φ₂ φ₃} → Γ ⊢ φ₁ ∨ φ₂ → Γ , φ₁ ⊢ φ₃ → Γ , φ₂ ⊢ φ₃ → Γ ⊢ φ₃
∨-elim Γ⊢∨ ⊢₁ ⊢₂ = ⊥-elim $ ⇒-elim axiom1 Γ,φ₃⇒⊥⊢φ₃ where
  Γ,φ₃⇒⊥⊢φ₃ = ⇒-elim (⇒-intro $ weakening2 ⊢₂) Γ,φ₃⇒⊥⊢φ₂ where
    Γ,φ₃⇒⊥⊢φ₂ = ⇒-elim (weakening1 Γ⊢∨) (⇒-intro $ ⇒-elim axiom2 (weakening2 ⊢₁))
```

### 矛盾律

```agda
no-contra : ∀ {Γ φ} → Γ ⊢ φ ∧ ~ φ → Γ ⊢ ⊥
no-contra ⊢ = ⇒-elim (∧-elimᵣ ⊢) (∧-elimₗ ⊢)

tauto-no-contra : ∀ {Γ φ} → Γ ⊢ ~ (φ ∧ ~ φ)
tauto-no-contra = ⇒-intro-tauto no-contra
```

### `⇔` 的引入引出规则

```agda
⇔-intro : ∀ {Γ φ₁ φ₂} → Γ , φ₁ ⊢ φ₂ → Γ , φ₂ ⊢ φ₁ → Γ ⊢ φ₁ ⇔ φ₂
⇔-intro ⊢₁ ⊢₂ = ∧-intro (⇒-intro ⊢₁) (⇒-intro ⊢₂)

⇔-elimₗ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ⇔ φ₂ → Γ , φ₁ ⊢ φ₂
⇔-elimₗ ⊢⇔ = ⇒-elim-to-axiom (∧-elimₗ ⊢⇔)

⇔-elimᵣ : ∀ {Γ φ₁ φ₂} → Γ ⊢ φ₁ ⇔ φ₂ → Γ , φ₂ ⊢ φ₁
⇔-elimᵣ ⊢⇔ = ⇒-elim-to-axiom (∧-elimᵣ ⊢⇔)
```

### `⇔` 的自反性、对称性和传递性

```agda
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

### `∃` 的引入引出规则

```agda
∃-intro : ∀ {Γ φ} (t : Term) → Γ ⊢ φ [ t / 0 ] → Γ ⊢ ∃' φ
∃-intro t ⊢ = ⇒-intro $ ⇒-elim (∀-elim axiom1) (weakening1 ⊢)

∃-elim : ∀ {Γ φ₁ φ₂} → Γ ⊢ ∃' φ₁ → Γ ⇑ 1 , φ₁ ⊢ φ₂ ↥ 1 → Γ ⊢ φ₂
∃-elim ⊢∃ ⊢ = ⊥-elim $ ⇒-elim
  (weakening1 ⊢∃)
  (∀-intro $ ⇒-intro $ ⇒-elim
    (weakening1 $ weakening ⊆⟦,⟧ axiom1)
    (weakening (,⊆, $ ⟦⟧⊆⟦⟧ ⊆,) ⊢)
  )
```
