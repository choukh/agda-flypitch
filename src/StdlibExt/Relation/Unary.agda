{-# OPTIONS --cubical-compatible --safe #-}

module StdlibExt.Relation.Unary where

open import Level
open import Data.Empty.Polymorphic using (⊥)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Unary using (Pred; _∈_; _⊆_; ｛_｝; _∪_) public

private variable
  a b ℓ : Level
  A : Set a
  B : Set b
  P Q : Pred A ℓ
  x : A
  f : A → B

infixl 6 _⨭_

∅ : Pred A ℓ
∅ = λ _ → ⊥

_⨭_ : ∀ {a} {A : Set a} (P : Pred A ℓ) (x : A) → Pred A (ℓ ⊔ a)
P ⨭ x = P ∪ ｛ x ｝

⊆⨭ : P ⊆ P ⨭ x
⊆⨭ x∈P = inj₁ x∈P

⨭⊆⨭ : P ⊆ Q → P ⨭ x ⊆ Q ⨭ x
⨭⊆⨭ P⊆Q (inj₁ x∈P)  = inj₁ (P⊆Q x∈P)
⨭⊆⨭ P⊆Q (inj₂ refl) = inj₂ refl

_⟦_⟧ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (P : Pred A ℓ) → Pred B (ℓ ⊔ a ⊔ b)
f ⟦ P ⟧ = λ y → ∃[ x ] x ∈ P × y ≡ f x

⟦⟧⊆⟦⟧ : P ⊆ Q → f ⟦ P ⟧ ⊆ f ⟦ Q ⟧
⟦⟧⊆⟦⟧ P⊆Q (x , x∈P , refl) = x , P⊆Q x∈P , refl

⟦⨭⟧⊆ : f ⟦ P ⨭ x ⟧ ⊆ f ⟦ P ⟧ ⨭ f x
⟦⨭⟧⊆ (x , inj₁ x∈P  , refl) = inj₁ (x , x∈P , refl)
⟦⨭⟧⊆ (x , inj₂ refl , refl) = inj₂ refl

⊆⟦⨭⟧ : f ⟦ P ⟧ ⨭ f x ⊆ f ⟦ P ⨭ x ⟧
⊆⟦⨭⟧ (inj₁ (x , x∈P , refl)) = x , inj₁ x∈P , refl
⊆⟦⨭⟧ {x = x} (inj₂ refl) = x , inj₂ refl , refl

_⟦｛_｝⟧ : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (x : A) → Pred B (a ⊔ b)
f ⟦｛ x ｝⟧ = f ⟦ ｛ x ｝ ⟧

⟦｛｝⟧⊆ : f ⟦｛ x ｝⟧ ⊆ ｛ f x ｝
⟦｛｝⟧⊆ (x , refl , refl) = refl

⊆⟦｛｝⟧ : ｛ f x ｝ ⊆ f ⟦｛ x ｝⟧
⊆⟦｛｝⟧ {x = x} refl = x , refl , refl
