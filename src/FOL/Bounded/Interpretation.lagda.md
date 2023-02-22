---
title: Agda一阶逻辑(5) 束缚项解释
zhihu-tags: Agda, 数理逻辑
---

# Agda一阶逻辑(5) 束缚项解释

> 交流Q群: 893531731  
> 本文源码: [Interpretation.lagda.md](https://github.com/choukh/agda-flypitch/blob/main/src/FOL/Bounded/Interpretation.lagda.md)  
> 高亮渲染: [Interpretation.html](https://choukh.github.io/agda-flypitch/FOL.Bounded.Interpretation.html)  

## 前言

```agda
{-# OPTIONS --cubical-compatible --safe #-}
{-# OPTIONS --lossy-unification #-}

open import FOL.Signature
module FOL.Bounded.Interpretation {u} (σ : Signature {u}) where
open import FOL.Bounded.Base σ
open import FOL.Interpretation σ using (Interpretation) public
open Interpretation
```

### 标准库依赖

```agda
open import Level
open import Data.Bool using (Bool; T; true; false)
open import Data.Empty using (⊥-elim)
open import Data.Empty.Polymorphic renaming (⊥ to False) hiding (⊥-elim)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.Unit.Polymorphic using (tt)
open import Function using (_$_)
open import Relation.Unary using (Pred; _∈_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_)
```

## 实现

```agda
module PreRealizer (𝒮 : Interpretation) where
  open Termₗ
  open Formulaₗ

  realizeₜ : ∀ (𝓋 : Vec (𝒮 .domain) n) (t : Termₗ n l) (xs : Vec (𝒮 .domain) l) → 𝒮 .domain
  realizeₜ 𝓋 (var k)      xs = lookup 𝓋 k
  realizeₜ 𝓋 (func f)     xs = 𝒮 .funmap f xs
  realizeₜ 𝓋 (app t₁ t₂)  xs = realizeₜ 𝓋 t₁ ((realizeₜ 𝓋 t₂ []) ∷ xs)

  realize : ∀ (𝓋 : Vec (𝒮 .domain) n) (φ : Formulaₗ n l) (xs : Vec (𝒮 .domain) l) → Set u
  realize 𝓋 ⊥          xs = False
  realize 𝓋 (rel R)    xs = Lift _ $ T $ 𝒮 .relmap R xs
  realize 𝓋 (appᵣ φ t) xs = realize 𝓋 φ (realizeₜ 𝓋 t [] ∷ xs)
  realize 𝓋 (t₁ ≈ t₂)  xs = realizeₜ 𝓋 t₁ xs ≡ realizeₜ 𝓋 t₂ xs
  realize 𝓋 (φ₁ ⇒ φ₂)  xs = realize 𝓋 φ₁ xs → realize 𝓋 φ₂ xs
  realize 𝓋 (∀' φ)     xs = ∀ x → realize (x ∷ 𝓋) φ xs

  dec : ∀ (𝓋 : Vec (𝒮 .domain) n) (φ : Formulaₗ n l) (xs : Vec (𝒮 .domain) l) → Dec (realize 𝓋 φ xs)
  dec 𝓋 ⊥ xs = no λ ()
  dec 𝓋 (rel R) xs with 𝒮 .relmap R xs
  ... | true  = yes tt
  ... | false = no λ ()
  dec 𝓋 (appᵣ φ t) xs = dec 𝓋 φ (realizeₜ 𝓋 t [] ∷ xs)
  dec 𝓋 (t₁ ≈ t₂) [] = 𝒮 .deceq (realizeₜ 𝓋 t₁ []) (realizeₜ 𝓋 t₂ [])
  dec 𝓋 (φ₁ ⇒ φ₂) xs with dec 𝓋 φ₁ xs | dec 𝓋 φ₂ xs
  ... | _     | yes q = yes λ _ → q
  ... | yes p | no ¬q = no  λ p→q → ¬q $ p→q p
  ... | no ¬p | no _  = yes λ p → ⊥-elim $ ¬p p
  dec 𝓋 (∀' φ) [] = 𝒮 .compactness _ (λ x → dec (x ∷ 𝓋) φ [])
```

```agda
module OpenedRealizer (𝒮 : Interpretation) {n} (𝓋 : Vec (𝒮 .domain) n) where
  open PreRealizer 𝒮 renaming (realizeₜ to rₜ; realize to r; dec to d)

  realizeₜ : Term n → 𝒮 .domain
  realizeₜ t = rₜ 𝓋 t []

  realize : Formula n → Set u
  realize φ = r 𝓋 φ []

  dec : ∀ φ → Dec (realize φ)
  dec φ = d 𝓋 φ []
```

```agda
module ClosedRealizer (𝒮 : Interpretation) where
  open OpenedRealizer 𝒮 [] renaming (realizeₜ to rₜ; realize to r; dec to d)

  realizeₜ : ClosedTerm → 𝒮 .domain
  realizeₜ t = rₜ t

  realize : Sentence → Set u
  realize φ = r φ

  dec : ∀ φ → Dec (realize φ)
  dec φ = d φ

  valid : Theory → Set u
  valid Γ = ∀ φ → φ ∈ Γ → realize φ
```

## 可满足性

```agda
open ClosedRealizer

_⊨_ : Theory → Sentence → Set (suc u)
Γ ⊨ φ = ∀ 𝒮 → valid 𝒮 Γ → realize 𝒮 φ
```
