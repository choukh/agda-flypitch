{-# OPTIONS --cubical-compatible --safe #-}

module FOL.Language.Homomorphism {u} where
open import FOL.Language hiding (u)
open Language {u}

open import Function using () renaming (_∘_ to _⟨∘⟩_)

record _⟶_ (ℒ₁ : Language) (ℒ₂ : Language) : Set u where
  field
    funhom : ∀ {n} → ℒ₁ .functions n → ℒ₂ .functions n
    relhom : ∀ {n} → ℒ₁ .relations n → ℒ₂ .relations n

open _⟶_ public

_∘_ : ∀ {ℒ₁ ℒ₂ ℒ₃} → ℒ₂ ⟶ ℒ₃ → ℒ₁ ⟶ ℒ₂ → ℒ₁ ⟶ ℒ₃
F ∘ G = record
  { funhom = F .funhom ⟨∘⟩ G .funhom
  ; relhom = F .relhom ⟨∘⟩ G .relhom }

--termhom : ∀ {ℒ₁ ℒ₂} → ℒ₁ ⟶ ℒ₂ → ℒ₁ .Term → ℒ₂ .Term
