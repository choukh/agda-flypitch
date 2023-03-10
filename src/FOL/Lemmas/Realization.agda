{-# OPTIONS --cubical-compatible --safe #-}

open import FOL.Language
open import FOL.Interpretation using (Interpretation)
module FOL.Lemmas.Realization (๐ฎ : Interpretation {u} โ) where

open import FOL.Base โ hiding (โฅ-elim; subst)
open import FOL.Lemmas.Lifting โ
open import FOL.Lemmas.Substitution โ
open import FOL.Interpretation โ
open FOL.Interpretation.Interpretation ๐ฎ

open import Data.Nat
open import Data.Empty using (โฅ-elim)
open import Function using (_$_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary using (tri<; triโ; tri>)
open import Relation.Binary.PropositionalEquality as Eq
  using (_โก_; refl; sym; cong; subst)
open import StdlibExt.Data.Vec using (Vec; []; _โท_; []-refl)
open import StdlibExt.Data.Nat.Properties
open import StdlibExt.Relation.Binary.PropositionalEquivalence u as Eqv hiding (sym)

module Preโ where
  open PreRealizer ๐ฎ renaming (realizeโ to rโ; realize to r) public
  open Eq.โก-Reasoning

  realizeโ-cong : โ (๐ ๐ : โ โ Domain) (ext : โ n โ ๐ n โก ๐ n)
    (t : Termโ l) (xs : Vec Domain l)
    โ rโ ๐ t xs โก rโ ๐ t xs
  realizeโ-cong ๐ ๐ ext (var k)     xs = ext k
  realizeโ-cong ๐ ๐ ext (func f)    xs = refl
  realizeโ-cong ๐ ๐ ext (app tโ tโ) xs
    rewrite realizeโ-cong ๐ ๐ ext tโ []
    rewrite realizeโ-cong ๐ ๐ ext tโ (rโ ๐ tโ [] โท xs) = refl

  realizeโ-subst : โ (๐ : โ โ Domain) (n : โ) (t : Termโ l)
    (s : Term) (xs : Vec Domain l)
    โ rโ (๐ [ rโ ๐ (s โ n) [] / n ]แตฅ) t xs โก rโ ๐ (t [ s / n ]โ) xs
  realizeโ-subst ๐ n (var k) s xs with <-cmp k n
  ... | tri< _ _ _ = refl
  ... | tri> _ _ _ = refl
  ... | triโ _ _ _ = cong (rโ ๐ (s โ[ 0 ] n)) ([]-refl xs)
  realizeโ-subst ๐ n (func f) s xs = refl
  realizeโ-subst ๐ n (app tโ tโ) s xs =
    let ๐' = ๐ [ rโ ๐ (s โ n) [] / n ]แตฅ in              begin
    rโ ๐' tโ             (rโ ๐' tโ [] โท xs)             โกโจ cong (rโ ๐' tโ) $ cong (_โท xs) (realizeโ-subst ๐ n tโ s []) โฉ
    rโ ๐' tโ             (rโ ๐ (tโ [ s / n ]โ) [] โท xs) โกโจ realizeโ-subst ๐ n tโ s _ โฉ
    rโ ๐ (tโ [ s / n ]โ) (rโ ๐ (tโ [ s / n ]โ) [] โท xs) โ

  realizeโ-subst-lift : โ (๐ : โ โ Domain) (n : โ) (t : Termโ l)
    (x : Domain) (xs : Vec Domain l)
    โ rโ (๐ [ x / n ]แตฅ) (t โ[ n ] 1) xs โก rโ ๐ t xs
  realizeโ-subst-lift ๐ n (var k) x xs with <-cmp k n | k <? n
  ... | triโ ยฌp _ _ | yes p = โฅ-elim $ ยฌp p
  ... | tri> ยฌp _ _ | yes p = โฅ-elim $ ยฌp p
  ... | tri< p ยฌq _ | yes _ with <-cmp k n
  ... | triโ _ q _  = โฅ-elim $ ยฌq q
  ... | tri> ยฌp _ _ = โฅ-elim $ ยฌp p
  ... | tri< _ _ _  = refl
  realizeโ-subst-lift ๐ n (var k) x xs | _ | no ยฌp with <-cmp (k + 1) n
  ... | tri< q _ _    = โฅ-elim $ ยฌp (<-trans n<n+1 q)
  ... | triโ _ refl _ = โฅ-elim $ ยฌp (subst (_โค k + 1) (+-comm k 1) โค-refl)
  ... | tri> _ _ _    = cong ๐ (m+nโธnโกm k 1)
  realizeโ-subst-lift ๐ n (func f) x xs = refl
  realizeโ-subst-lift ๐ n (app tโ tโ) x xs =
    let ๐' = ๐ [ x / n ]แตฅ in                          begin
    rโ ๐' (tโ โ[ n ] 1) (rโ ๐' (tโ โ[ n ] 1) [] โท xs) โกโจ realizeโ-subst-lift ๐ n tโ x _ โฉ
    rโ ๐ tโ             (rโ ๐' (tโ โ[ n ] 1) [] โท xs) โกโจ cong (rโ ๐ tโ) $ cong (_โท xs) (realizeโ-subst-lift ๐ n tโ x []) โฉ
    rโ ๐ tโ             (rโ ๐ tโ [] โท xs)             โ

module Pre where
  open Preโ public
  open Eqv.โ-Reasoning

  realize-cong : โ (๐ ๐ : โ โ Domain) (ext : โ n โ ๐ n โก ๐ n)
    (ฯ : Formulaโ l) (xs : Vec Domain l)
    โ r ๐ ฯ xs โ r ๐ ฯ xs
  realize-cong ๐ ๐ ext โฅ           xs = id
  realize-cong ๐ ๐ ext (rel R)     xs = id
  realize-cong ๐ ๐ ext (appแตฃ ฯ t)  xs
    rewrite realizeโ-cong ๐ ๐ ext t [] = realize-cong ๐ ๐ ext ฯ _
  realize-cong ๐ ๐ ext (tโ โ tโ) xs
    rewrite realizeโ-cong ๐ ๐ ext tโ xs
          | realizeโ-cong ๐ ๐ ext tโ xs = id
  realize-cong ๐ ๐ ext (ฯโ โ ฯโ) xs =
    โ-cong (realize-cong ๐ ๐ ext ฯโ xs) (realize-cong ๐ ๐ ext ฯโ xs)
  realize-cong ๐ ๐ ext (โ' ฯ) xs = โ-cong $ ฮป x
    โ realize-cong (๐ [ x / 0 ]แตฅ) (๐ [ x / 0 ]แตฅ) (/แตฅ-cong ext x 0) ฯ xs

  realize-subst : โ (๐ : โ โ Domain) (n : โ) (ฯ : Formulaโ l)
    (s : Term) (xs : Vec Domain l)
    โ r (๐ [ rโ ๐ (s โ n) [] / n ]แตฅ) ฯ xs โ r ๐ (ฯ [ s / n ]) xs
  realize-subst ๐ n โฅ          s xs = id
  realize-subst ๐ n (rel Rโ)   s xs = id
  realize-subst ๐ n (appแตฃ ฯ t) s xs
    rewrite realizeโ-subst ๐ n t s [] = realize-subst ๐ n ฯ s _
  realize-subst ๐ n (tโ โ tโ) s xs
    rewrite realizeโ-subst ๐ n tโ s xs
          | realizeโ-subst ๐ n tโ s xs = id
  realize-subst ๐ n (ฯโ โ ฯโ) s xs =
    โ-cong (realize-subst ๐ n ฯโ s xs) (realize-subst ๐ n ฯโ s xs)
  realize-subst ๐ n (โ' ฯ) s xs = โ-cong $ ฮป x โ
    let tโ = rโ (๐ [ x / 0 ]แตฅ) (s โ suc n)   []
        tโ = rโ (๐ [ x / 0 ]แตฅ) ((s โ n) โ 1) []
        ๐โ = ๐ [ tโ / n ]แตฅ [ x / 0 ]แตฅ
        ๐โ = ๐ [ tโ / n ]แตฅ [ x / 0 ]แตฅ
        tโก : tโ โก tโ
        tโก = cong (ฮป t โ rโ (๐ [ x / 0 ]แตฅ) t []) (โโห s n 1)
        ๐โกโ : โ m โ ๐โ m โก ๐โ m
        ๐โกโ m = cong (ฮป t โ (๐ [ t / n ]แตฅ [ x / 0 ]แตฅ) m) tโก
        ๐โ = ๐ [ rโ ๐ (s โ n) [] / n ]แตฅ [ x / 0 ]แตฅ
        ๐โกโ : โ m โ ๐โ m โก ๐โ m
        ๐โกโ m = sym $ cong (ฮป t โ (๐ [ t / n ]แตฅ [ x / 0 ]แตฅ) m) (realizeโ-subst-lift ๐ 0 (s โ n) x [])
    in begin
    r ๐โ ฯ xs                             โโจ realize-cong _ _ ๐โกโ ฯ xs โฉ
    r ๐โ ฯ xs                             โโจ realize-cong _ _ ๐โกโ ฯ xs โฉ
    r ๐โ ฯ xs                             โโจ realize-cong _ _ (//แตฅ ๐ x tโ 0 n) ฯ xs โฉ
    r (๐ [ x / 0 ]แตฅ [ tโ / suc n ]แตฅ) ฯ xs โโจ realize-subst (๐ [ x / 0 ]แตฅ) (suc n) ฯ s xs โฉ
    r (๐ [ x / 0 ]แตฅ) (ฯ [ s / suc n ]) xs โ

  realize-subst-lift : โ (๐ : โ โ Domain) (n : โ)
    (ฯ : Formulaโ l) (x : Domain) (xs : Vec Domain l)
    โ r (๐ [ x / n ]แตฅ) (ฯ โฅ[ n ] 1) xs โ r ๐ ฯ xs
  realize-subst-lift ๐ n โฅ x xs        = id
  realize-subst-lift ๐ n (rel Rโ) x xs = id
  realize-subst-lift ๐ n (appแตฃ ฯ t) x xs
    rewrite realizeโ-subst-lift ๐ n t x [] = realize-subst-lift ๐ n ฯ x _
  realize-subst-lift ๐ n (tโ โ tโ) x xs
    rewrite realizeโ-subst-lift ๐ n tโ x xs
          | realizeโ-subst-lift ๐ n tโ x xs = id
  realize-subst-lift ๐ n (ฯโ โ ฯโ) x xs =
    โ-cong (realize-subst-lift ๐ n ฯโ x xs) (realize-subst-lift ๐ n ฯโ x xs)
  realize-subst-lift ๐ n (โ' ฯ) x xs = โ-cong $ ฮป y โ   begin
    r (๐ [ x / n ]แตฅ [ y / 0 ]แตฅ)     (ฯ โฅ[ suc n ] 1) xs โโจ realize-cong _ _ (//แตฅ ๐ y x 0 n) (ฯ โฅ[ suc n ] 1) xs โฉ
    r (๐ [ y / 0 ]แตฅ [ x / suc n ]แตฅ) (ฯ โฅ[ suc n ] 1) xs โโจ realize-subst-lift (๐ [ y / 0 ]แตฅ) (suc n) ฯ x xs โฉ
    r (๐ [ y / 0 ]แตฅ) ฯ xs                               โ

open Realizer ๐ฎ

realizeโ-cong : โ (๐ ๐ : โ โ Domain) (ext : โ n โ ๐ n โก ๐ n) (t : Term)
  โ realizeโ ๐ t โก realizeโ ๐ t
realizeโ-cong ๐ ๐ ext t = Pre.realizeโ-cong ๐ ๐ ext t []

realizeโ-subst : โ (๐ : โ โ Domain) (n : โ) (t : Term) (s : Term)
  โ realizeโ (๐ [ realizeโ ๐ (s โ n) / n ]แตฅ) t โก realizeโ ๐ (t [ s / n ]โ)
realizeโ-subst ๐ n t s = Pre.realizeโ-subst ๐ n t s []

realizeโ-subst-lift : โ (๐ : โ โ Domain) (n : โ) (t : Term) (x : Domain)
  โ realizeโ (๐ [ x / n ]แตฅ) (t โ[ n ] 1) โก realizeโ ๐ t
realizeโ-subst-lift ๐ n t x = Pre.realizeโ-subst-lift ๐ n t x []

realize-cong : โ (๐ ๐ : โ โ Domain) (ext : โ n โ ๐ n โก ๐ n) (ฯ : Formula)
  โ realize ๐ ฯ โ realize ๐ ฯ
realize-cong ๐ ๐ ext ฯ = Pre.realize-cong ๐ ๐ ext ฯ []

realize-subst : โ (๐ : โ โ Domain) (n : โ) (ฯ : Formula) (s : Term)
  โ realize (๐ [ realizeโ ๐ (s โ n) / n ]แตฅ) ฯ โ realize ๐ (ฯ [ s / n ])
realize-subst ๐ n ฯ s = Pre.realize-subst ๐ n ฯ s []

realize-subst-lift : โ (๐ : โ โ Domain) (n : โ) (ฯ : Formula) (x : Domain)
  โ realize (๐ [ x / n ]แตฅ) (ฯ โฅ[ n ] 1) โ realize ๐ ฯ
realize-subst-lift ๐ n ฯ x = Pre.realize-subst-lift ๐ n ฯ x []

open Eqv.โ-Reasoning

realize-subst0 : โ (๐ : โ โ Domain) (ฯ : Formula) (s : Term)
  โ realize (๐ [ realizeโ ๐ s / 0 ]แตฅ) ฯ โ realize ๐ (ฯ [ s / 0 ])
realize-subst0 ๐ ฯ s =                      begin
  realize (๐ [ realizeโ ๐ s       / 0 ]แตฅ) ฯ โกหโจ cong (ฮป s โ realize (๐ [ realizeโ ๐ s / 0 ]แตฅ) ฯ) (โ0 s) โฉ
  realize (๐ [ realizeโ ๐ (s โ 0) / 0 ]แตฅ) ฯ โโจ realize-subst ๐ 0 ฯ s โฉ
  realize ๐ (ฯ [ s / 0 ])                   โ
