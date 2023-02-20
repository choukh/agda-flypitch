{-# OPTIONS --cubical-compatible --safe #-}

module StdlibExt.Relation.Unary where

open import Level using (Level; _⊔_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Unary using (Pred; _∈_; _⊆_; ｛_｝; _∪_)

infixl 6 _⨭_

_⨭_ : ∀ {u v} {A : Set u} (P : Pred A v) (a : A) → Pred A (u ⊔ v)
P ⨭ a = P ∪ ｛ a ｝

⊆⨭ : ∀ {u v} {A : Set u} {P : Pred A v} {a : A} → P ⊆ P ⨭ a
⊆⨭ x∈P = inj₁ x∈P

⨭⊆⨭ : ∀ {u v} {A : Set u} {P Q : Pred A v} {a : A} → P ⊆ Q → P ⨭ a ⊆ Q ⨭ a
⨭⊆⨭ P⊆Q (inj₁ x∈P)  = inj₁ (P⊆Q x∈P)
⨭⊆⨭ P⊆Q (inj₂ refl) = inj₂ refl

_⟦_⟧ : ∀ {u v} {A : Set u} (f : A → A) (P : Pred A v) → Pred A (u ⊔ v)
f ⟦ P ⟧ = λ y → ∃[ x ] x ∈ P × y ≡ f x

⟦⟧⊆⟦⟧ : ∀ {u v} {A : Set u} {f : A → A} {P Q : Pred A v} → P ⊆ Q → f ⟦ P ⟧ ⊆ f ⟦ Q ⟧
⟦⟧⊆⟦⟧ P⊆Q (x , x∈P , refl) = x , P⊆Q x∈P , refl

⟦⨭⟧⊆ : ∀ {u v} {A : Set u} {f : A → A} {P : Pred A v} {a : A} → f ⟦ P ⨭ a ⟧ ⊆ f ⟦ P ⟧ ⨭ f a
⟦⨭⟧⊆ (x , inj₁ x∈P  , refl) = inj₁ (x , x∈P , refl)
⟦⨭⟧⊆ (x , inj₂ refl , refl) = inj₂ refl

⊆⟦⨭⟧ : ∀ {u v} {A : Set u} {f : A → A} {P : Pred A v} {a : A} → f ⟦ P ⟧ ⨭ f a ⊆ f ⟦ P ⨭ a ⟧
⊆⟦⨭⟧ (inj₁ (x , x∈P , refl)) = x , inj₁ x∈P , refl
⊆⟦⨭⟧ {a = a} (inj₂ refl) = a , inj₂ refl , refl