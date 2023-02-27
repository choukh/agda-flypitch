{-# OPTIONS --cubical-compatible --safe #-}

module Tools.DirectedDiagram where

open import Level renaming (suc to lsuc)
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Function using (_∘_)
open import Relation.Binary using (Rel; Reflexive; Transitive)
open import Relation.Binary.PropositionalEquality using (_≡_)

private variable
  u v w : Level

record DirectedType : Set (lsuc u ⊔ lsuc v) where
  field
    Carrier : Set u
    _~_ : Rel Carrier v
    ~-refl : Reflexive _~_
    ~-trans : Transitive _~_
    directed : ∀ x y → ∃[ z ] x ~ z × y ~ z

record DirectedDiagram (d : DirectedType {u} {v}) : Set (u ⊔ v ⊔ lsuc w) where
  open DirectedType d
  field
    obj : Carrier → Set w
    morph : ∀ {x y} → x ~ y → obj x → obj y
    functorial : ∀ {x y z} {f₁ : x ~ y} {f₂ : y ~ z} {f₃ : x ~ z}
      → (morph f₃) ≡ (morph f₂) ∘ (morph f₁)

directedTypeOfℕ : DirectedType
directedTypeOfℕ = record
  { Carrier = ℕ
  ; _~_ = _≤_
  ; ~-refl = ≤-refl
  ; ~-trans = ≤-trans
  ; directed = λ x y → x + y , (m≤m+n _ _) , (m≤n+m _ _)
  }
