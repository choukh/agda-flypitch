{-# OPTIONS --cubical-compatible --safe #-}

module StdlibExt.Relation.Nullary where

open import Data.Empty.Polymorphic using (⊥; ⊥-elim)
open import Relation.Nullary public

byContra : ∀ {u v} {A : Set u} → ⦃ Dec A ⦄ → (¬ A → ⊥ {v}) → A
byContra ⦃ yes a ⦄ ¬A⇒⊥ = a
byContra ⦃ no ¬a ⦄ ¬A⇒⊥ = ⊥-elim (¬A⇒⊥ ¬a)
