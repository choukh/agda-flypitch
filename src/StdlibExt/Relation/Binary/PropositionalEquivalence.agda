{-# OPTIONS --cubical-compatible --safe #-}

module StdlibExt.Relation.Binary.PropositionalEquivalence (u) where

open import Function.Equivalence
  renaming (_⇔_ to _↔_; ⇔-setoid to ↔-setoid; equivalence to mk↔) public
open import Relation.Binary.Reasoning.Setoid (↔-setoid u)
  using (step-≈) renaming (begin_ to begin-↔_; _∎ to _∎-↔) public
open import Function.Equality using (_⟨$⟩_) public
