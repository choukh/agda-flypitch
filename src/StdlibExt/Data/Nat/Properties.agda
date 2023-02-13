{-# OPTIONS --cubical-compatible --safe #-}

module StdlibExt.Data.Nat.Properties where

open import Data.Nat
open import Data.Nat.Properties

n<n+1 : ∀ {n} → n < n + 1
n<n+1 {n} = m<m+n n (s≤s z≤n)