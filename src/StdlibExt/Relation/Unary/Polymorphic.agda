{-# OPTIONS --cubical-compatible --safe #-}

module StdlibExt.Relation.Unary.Polymorphic where

open import Level
open import Data.Empty.Polymorphic using (⊥)
open import Data.Unit.Polymorphic using (⊤)
open import Relation.Unary using (Pred)

private variable
  a ℓ : Level
  A : Set a

∅ : Pred A ℓ
∅ = λ _ → ⊥

U : Pred A ℓ
U = λ _ → ⊤
