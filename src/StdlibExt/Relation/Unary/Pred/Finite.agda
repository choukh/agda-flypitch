{-# OPTIONS --cubical-compatible --safe #-}

module StdlibExt.Relation.Unary.Pred.Finite where

open import Level
open import StdlibExt.Relation.Unary.Pred

data Finite {a} {A : Set a} : Pred A a → Set (suc a) where
  empty : Finite ∅
  union : ∀ P x → x ∈ P → Finite P → Finite (P ⨭ x)
