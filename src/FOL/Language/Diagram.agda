{-# OPTIONS --cubical-compatible --safe #-}

module FOL.Language.Diagram where
open import FOL.Language hiding (u)
open import FOL.Language.Homomorphism
open import Tools.DirectedDiagram

open import Level
open import Relation.Binary.PropositionalEquality using (_≡_)

private variable
  u v w : Level

record Diagram (d : DirectedType {u} {v}) : Set (u ⊔ v ⊔ suc w) where
  open DirectedType d
  field
    obj : Carrier → Language {w}
    morph : ∀ {x y} → x ~ y → obj x ⟶ obj y
    functorial : ∀ {x y z} {f₁ : x ~ y} {f₂ : y ~ z} {f₃ : x ~ z}
      → (morph f₃) ≡ (morph f₂) ∘ (morph f₁)
