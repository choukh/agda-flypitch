---
title: Agda一阶逻辑(1) 签名
zhihu-tags: Agda, 数理逻辑
zhihu-url: https://zhuanlan.zhihu.com/p/604316553
---

# Agda一阶逻辑(1) 签名

> 交流Q群: 893531731  
> 本文源码: [Signature.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/FOL/Signature.lagda.md)  
> 高亮渲染: [Signature.html](https://choukh.github.io/agda-flypitch/FOL.Signature.html)  

一阶逻辑是一种形式语言, 其语句由一些原始符号按一定的语法组合而成. 符号又分为逻辑符号和非逻辑符号. 本篇先讲非逻辑符号.

非逻辑符号分为函数符号和关系符号, 且它们都带有一个称为元数 (arity) 的属性. 例如, 元数为 2 的函数符号即用于表示二元函数. 特别地, 元数为零的函数又称为常量.

较传统的处理方式是给出所有可能的函数符号和关系符号. 即对任意元数 $n$, 都有自然数多个函数符号

$$f^n_0,\ f^n_1,\ f^n_2,\ f^n_3,\ ...$$

以及自然数多个关系符号

$$R^n_0,\ R^n_1,\ R^n_2,\ R^n_3,\ ...$$

在这种处理下, 只有唯一一种一阶逻辑语言.

较现代的方式是根据最终要实现的一阶理论来指定该理论所需的非逻辑符号. 这些特定的符号以及它们的元数所组成的资料叫做理论的**签名 (signature)**. 在这种处理下, 每种签名都对应一种一阶逻辑语言. 形式地, 一阶逻辑的其他部分都是参数化到签名上的, 因此我们把签名单独作为一个模块.

```agda
{-# OPTIONS --cubical-compatible --safe #-}

module FOL.Signature where

open import Level using (suc)
open import Data.Nat using (ℕ)
```

**定义 (签名)** 由按元数分类的函数符号集族 `functions : ℕ → Set u` 以及按元数分类的关系符号集族 `relations : ℕ → Set u` 组成的资料叫做签名. 其中 `u` 是宇宙多态参数. 签名比符号集高一个宇宙. 常量集是元数为 0 的函数集.

```agda
record Signature {u} : Set (suc u) where
  field
    functions : ℕ → Set u
    relations : ℕ → Set u
  constants = functions 0
```

**例** 下面给出了签名的一个实例, 它可以作为皮亚诺算术 (一种一阶理论) 的签名. 注意符号的元数被编码到了类型里面. 例如, 常量 `O` 的类型是 `func 0`, 后继函数 `S` 的类型是 `func 1`, 加法 `+` 以及乘法 `*` 的类型是 `func 2`, 小于关系 `<` 的类型是 `rel 2`.

```agda
module ExampleSignaturePA where

  data func : ℕ → Set where
    O : func 0
    S : func 1
    + : func 2
    * : func 2

  data rel : ℕ → Set where
    < : rel 2

  σ : Signature
  σ = record
    { functions = func
    ; relations = rel
    }
```
