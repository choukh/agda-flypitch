{-# OPTIONS --cubical-compatible --safe #-}

open import FOL.Language
open import FOL.Interpretation using (Interpretation)
module FOL.Bounded.Lemmas.Realization (๐ฎ : Interpretation {u} โ) where

open import FOL.Base โ using (_[_/_]แตฅ)
open import FOL.Bounded.Base โ
open import FOL.Bounded.Interpretation โ
import FOL.Interpretation โ as Free
open FOL.Interpretation.Interpretation ๐ฎ

open import Data.Nat
open import Data.Fin using (Fin; zero; suc; toโ)
open import Data.Vec using (Vec; []; _โท_; lookup)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_โก_; refl; cong)
open import StdlibExt.Relation.Binary.PropositionalEquivalence u as Eqv

module Pre where
  open PreRealizer ๐ฎ using () renaming (realizeโ to rโ; realize to r) public
  open Free.PreRealizer ๐ฎ using () renaming (realizeโ to ๐โ; realize to ๐) public
  open Eqv.โ-Reasoning

  realizeโ-eq : โ (๐ : Vec Domain n) (๐ฃ : โ โ Domain)
    (eq : โ k โ lookup ๐ k โก ๐ฃ (toโ k)) (t : Termโ n l) (xs : Vec Domain l)
    โ rโ ๐ t xs โก ๐โ ๐ฃ (unboundโ t) xs
  realizeโ-eq ๐ ๐ฃ eq (var k)     xs = eq k
  realizeโ-eq ๐ ๐ฃ eq (func f)    xs = refl
  realizeโ-eq ๐ ๐ฃ eq (app tโ tโ) xs rewrite realizeโ-eq ๐ ๐ฃ eq tโ [] = realizeโ-eq ๐ ๐ฃ eq tโ _

  realize-iff : โ (๐ : Vec Domain n) (๐ฃ : โ โ Domain)
    (eq : โ k โ lookup ๐ k โก ๐ฃ (toโ k)) (ฯ : Formulaโ n l) (xs : Vec Domain l)
    โ r ๐ ฯ xs โ ๐ ๐ฃ (unbound ฯ) xs
  realize-iff ๐ ๐ฃ eq โฅ          xs = id
  realize-iff ๐ ๐ฃ eq (rel R)    xs = id
  realize-iff ๐ ๐ฃ eq (appแตฃ ฯ t) xs
    rewrite realizeโ-eq ๐ ๐ฃ eq t [] = realize-iff ๐ ๐ฃ eq ฯ _
  realize-iff ๐ ๐ฃ eq (tโ โ tโ)  [] =
    โก-cong (realizeโ-eq ๐ ๐ฃ eq tโ []) (realizeโ-eq ๐ ๐ฃ eq tโ [])
  realize-iff ๐ ๐ฃ eq (ฯโ โ ฯโ)  xs =
    โ-cong (realize-iff ๐ ๐ฃ eq ฯโ xs) (realize-iff ๐ ๐ฃ eq ฯโ xs)
  realize-iff ๐ ๐ฃ eq (โ' ฯ)     [] = โ-cong $ ฮป x โ
    realize-iff (x โท ๐) (๐ฃ [ x / 0 ]แตฅ) (eq' x) ฯ [] where
    eq' : โ x k โ lookup (x โท ๐) k โก (๐ฃ [ x / 0 ]แตฅ) (toโ k)
    eq' x zero    = refl
    eq' x (suc k) = eq k

module Opened where
  open OpenedRealizer ๐ฎ using () renaming (realizeโ to rโ; realize to r) public
  open Free.Realizer ๐ฎ using () renaming (realizeโ to ๐โ; realize to ๐) public

  realizeโ-eq : โ (๐ : Vec Domain n) (๐ฃ : โ โ Domain)
    (eq : โ k โ lookup ๐ k โก ๐ฃ (toโ k)) (t : Term n)
    โ rโ ๐ t โก ๐โ ๐ฃ (unboundโ t)
  realizeโ-eq ๐ ๐ฃ eq t = Pre.realizeโ-eq ๐ ๐ฃ eq t []

  realize-iff : โ (๐ : Vec Domain n) (๐ฃ : โ โ Domain)
    (eq : โ k โ lookup ๐ k โก ๐ฃ (toโ k)) (ฯ : Formula n)
    โ r ๐ ฯ โ ๐ ๐ฃ (unbound ฯ)
  realize-iff ๐ ๐ฃ eq ฯ = Pre.realize-iff ๐ ๐ฃ eq ฯ []

module Closed where
  open ClosedRealizer ๐ฎ using () renaming (realizeโ to rโ; realize to r) public
  open Free.Realizer ๐ฎ using () renaming (realizeโ to ๐โ; realize to ๐) public

  realizeโ-eq : โ (๐ฃ : โ โ Domain) (t : ClosedTerm) โ rโ t โก ๐โ ๐ฃ (unboundโ t)
  realizeโ-eq ๐ฃ t = Opened.realizeโ-eq [] ๐ฃ (ฮป ()) t

  realize-iff : โ (๐ฃ : โ โ Domain) (ฯ : Sentence) โ r ฯ โ ๐ ๐ฃ (unbound ฯ)
  realize-iff ๐ฃ ฯ = Opened.realize-iff [] ๐ฃ (ฮป ()) ฯ
