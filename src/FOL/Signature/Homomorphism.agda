{-# OPTIONS --cubical-compatible --safe #-}

module FOL.Signature.Homomorphism {u} where
open import FOL.Signature using (Signature)
open Signature {u}

open import Function using () renaming (_∘_ to _⟨∘⟩_)

record _⟶_ (ℒ₁ : Signature) (ℒ₂ : Signature) : Set u where
  field
    funhomo : ∀ {n} → ℒ₁ .functions n → ℒ₂ .functions n
    relhomo : ∀ {n} → ℒ₁ .relations n → ℒ₂ .relations n

open _⟶_ public

_∘_ : ∀ {ℒ₁ ℒ₂ ℒ₃} → ℒ₂ ⟶ ℒ₃ → ℒ₁ ⟶ ℒ₂ → ℒ₁ ⟶ ℒ₃
F ∘ G = record
  { funhomo = F .funhomo ⟨∘⟩ G .funhomo
  ; relhomo = F .relhomo ⟨∘⟩ G .relhomo }
