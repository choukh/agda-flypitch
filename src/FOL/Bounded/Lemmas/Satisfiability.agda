{-# OPTIONS --cubical-compatible --safe #-}

open import FOL.Signature
module FOL.Bounded.Lemmas.Satisfiability (ℒ : Signature {u}) where

import FOL.Interpretation ℒ as Free
open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Interpretation ℒ
open import FOL.Bounded.Lemmas.Realization ℒ
open Closed using (realize-iff)

open import Data.Product using (_,_)
open import Function.Equality using (_⟨$⟩_) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import StdlibExt.Relation.Unary using (_⟦_⟧)
open import StdlibExt.Relation.Binary.PropositionalEquivalence

bound⊨ : ∀ {Γ φ} → unbound ⟦ Γ ⟧ Free.⊨ unbound φ → Γ ⊨ φ
bound⊨ {Γ} {φ} ⊨ 𝒮 x vld = let 𝓋 = λ _ → x in
  from (realize-iff 𝒮 𝓋 φ) ⟨$⟩ ⊨ 𝒮 𝓋 λ { ψ' (ψ , ψ∈Γ , refl) →
  to   (realize-iff 𝒮 𝓋 ψ) ⟨$⟩ vld ψ ψ∈Γ }
