{-# OPTIONS --cubical-compatible --safe #-}

module FOL.Language.Homomorphism {u} where
open import FOL.Language hiding (u)
open Language {u}

open import Data.Nat
open import Function using () renaming (_∘_ to _⟨∘⟩_)
open import StdlibExt.Relation.Unary using (_⟦_⟧)

record _⟶_ (ℒ₁ : Language) (ℒ₂ : Language) : Set u where
  field
    funcMorph : ∀ {n} → ℒ₁ .functions n → ℒ₂ .functions n
    relMorph  : ∀ {n} → ℒ₁ .relations n → ℒ₂ .relations n

_∘_ : ∀ {ℒ₁ ℒ₂ ℒ₃} → ℒ₂ ⟶ ℒ₃ → ℒ₁ ⟶ ℒ₂ → ℒ₁ ⟶ ℒ₃
F ∘ G = record
  { funcMorph = F .funcMorph ⟨∘⟩ G .funcMorph
  ; relMorph  = F .relMorph  ⟨∘⟩ G .relMorph } where open _⟶_

module Bounded {ℒ₁ ℒ₂} (F : ℒ₁ ⟶ ℒ₂) where
  open import FOL.Bounded.Base {u} hiding (n; l)
  open _⟶_ {ℒ₁} {ℒ₂} F

  private variable
    n l : ℕ

  termMorph : Termₗ ℒ₁ n l → Termₗ ℒ₂ n l
  termMorph (var k)     = var k
  termMorph (func f)    = func (funcMorph f)
  termMorph (app t₁ t₂) = app (termMorph t₁) (termMorph t₂)

  formulaMorph : Formulaₗ ℒ₁ n l → Formulaₗ ℒ₂ n l
  formulaMorph ⊥          = ⊥
  formulaMorph (rel R)    = rel (relMorph R)
  formulaMorph (appᵣ φ t) = appᵣ (formulaMorph φ) (termMorph t)
  formulaMorph (t₁ ≈ t₂)  = termMorph t₁ ≈ termMorph t₂
  formulaMorph (φ₁ ⇒ φ₂)  = formulaMorph φ₁ ⇒ formulaMorph φ₂
  formulaMorph (∀' φ)     = ∀' formulaMorph φ

  closedTermMorph : ClosedTerm ℒ₁ → ClosedTerm ℒ₂
  closedTermMorph = termMorph

  sentenceMorph : Sentence ℒ₁ → Sentence ℒ₂
  sentenceMorph = formulaMorph

  theoryMorph : Theory ℒ₁ → Theory ℒ₂
  theoryMorph Γ = sentenceMorph ⟦ Γ ⟧
