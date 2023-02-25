{-# OPTIONS --cubical-compatible --safe #-}

open import FOL.Signature
open import FOL.Interpretation using (Interpretation)
module FOL.Bounded.Lemmas.Realization (𝒮 : Interpretation {u} ℒ) where

open import FOL.Base ℒ using (_[_/_]ᵥ)
open import FOL.Bounded.Base ℒ
open import FOL.Bounded.Interpretation ℒ
import FOL.Interpretation ℒ as Free
open FOL.Interpretation.Interpretation 𝒮

open import Data.Nat
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import StdlibExt.Relation.Binary.PropositionalEquivalence u as Eqv

module Pre where
  open PreRealizer 𝒮 using () renaming (realizeₜ to rₜ; realize to r) public
  open Free.PreRealizer 𝒮 using () renaming (realizeₜ to 𝑟ₜ; realize to 𝑟) public
  open Eqv.↔-Reasoning

  realizeₜ-eq : ∀ (𝓋 : Vec Domain n) (𝑣 : ℕ → Domain)
    (eq : ∀ k → lookup 𝓋 k ≡ 𝑣 (toℕ k)) (t : Termₗ n l) (xs : Vec Domain l)
    → rₜ 𝓋 t xs ≡ 𝑟ₜ 𝑣 (unboundₜ t) xs
  realizeₜ-eq 𝓋 𝑣 eq (var k)     xs = eq k
  realizeₜ-eq 𝓋 𝑣 eq (func f)    xs = refl
  realizeₜ-eq 𝓋 𝑣 eq (app t₁ t₂) xs rewrite realizeₜ-eq 𝓋 𝑣 eq t₂ [] = realizeₜ-eq 𝓋 𝑣 eq t₁ _

  realize-iff : ∀ (𝓋 : Vec Domain n) (𝑣 : ℕ → Domain)
    (eq : ∀ k → lookup 𝓋 k ≡ 𝑣 (toℕ k)) (φ : Formulaₗ n l) (xs : Vec Domain l)
    → r 𝓋 φ xs ↔ 𝑟 𝑣 (unbound φ) xs
  realize-iff 𝓋 𝑣 eq ⊥          xs = id
  realize-iff 𝓋 𝑣 eq (rel R)    xs = id
  realize-iff 𝓋 𝑣 eq (appᵣ φ t) xs
    rewrite realizeₜ-eq 𝓋 𝑣 eq t [] = realize-iff 𝓋 𝑣 eq φ _
  realize-iff 𝓋 𝑣 eq (t₁ ≈ t₂)  [] =
    ≡-cong (realizeₜ-eq 𝓋 𝑣 eq t₁ []) (realizeₜ-eq 𝓋 𝑣 eq t₂ [])
  realize-iff 𝓋 𝑣 eq (φ₁ ⇒ φ₂)  xs =
    →-cong (realize-iff 𝓋 𝑣 eq φ₁ xs) (realize-iff 𝓋 𝑣 eq φ₂ xs)
  realize-iff 𝓋 𝑣 eq (∀' φ)     [] = ∀-cong $ λ x →
    realize-iff (x ∷ 𝓋) (𝑣 [ x / 0 ]ᵥ) (eq' x) φ [] where
    eq' : ∀ x k → lookup (x ∷ 𝓋) k ≡ (𝑣 [ x / 0 ]ᵥ) (toℕ k)
    eq' x zero    = refl
    eq' x (suc k) = eq k

module Opened where
  open OpenedRealizer 𝒮 using () renaming (realizeₜ to rₜ; realize to r) public
  open Free.Realizer 𝒮 using () renaming (realizeₜ to 𝑟ₜ; realize to 𝑟) public

  realizeₜ-eq : ∀ (𝓋 : Vec Domain n) (𝑣 : ℕ → Domain)
    (eq : ∀ k → lookup 𝓋 k ≡ 𝑣 (toℕ k)) (t : Term n)
    → rₜ 𝓋 t ≡ 𝑟ₜ 𝑣 (unboundₜ t)
  realizeₜ-eq 𝓋 𝑣 eq t = Pre.realizeₜ-eq 𝓋 𝑣 eq t []

  realize-iff : ∀ (𝓋 : Vec Domain n) (𝑣 : ℕ → Domain)
    (eq : ∀ k → lookup 𝓋 k ≡ 𝑣 (toℕ k)) (φ : Formula n)
    → r 𝓋 φ ↔ 𝑟 𝑣 (unbound φ)
  realize-iff 𝓋 𝑣 eq φ = Pre.realize-iff 𝓋 𝑣 eq φ []

module Closed where
  open ClosedRealizer 𝒮 using () renaming (realizeₜ to rₜ; realize to r) public
  open Free.Realizer 𝒮 using () renaming (realizeₜ to 𝑟ₜ; realize to 𝑟) public

  realizeₜ-eq : ∀ (𝑣 : ℕ → Domain) (t : ClosedTerm) → rₜ t ≡ 𝑟ₜ 𝑣 (unboundₜ t)
  realizeₜ-eq 𝑣 t = Opened.realizeₜ-eq [] 𝑣 (λ ()) t

  realize-iff : ∀ (𝑣 : ℕ → Domain) (φ : Sentence) → r φ ↔ 𝑟 𝑣 (unbound φ)
  realize-iff 𝑣 φ = Opened.realize-iff [] 𝑣 (λ ()) φ
