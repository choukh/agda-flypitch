{-# OPTIONS --cubical-compatible --safe #-}

module StdlibExt.Data.Vec where
open import Data.Vec public
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

[]-refl : ∀ {u} {A : Set u} (xs : Vec A 0) → [] ≡ xs
[]-refl [] = refl
