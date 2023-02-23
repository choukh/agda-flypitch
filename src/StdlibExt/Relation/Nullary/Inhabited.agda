{-# OPTIONS --cubical-compatible --safe #-}

module StdlibExt.Relation.Nullary.Inhabited where

data inhabited {u} (A : Set u) : Set u where
  here : A → inhabited A
