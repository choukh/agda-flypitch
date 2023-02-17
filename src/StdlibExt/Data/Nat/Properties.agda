{-# OPTIONS --cubical-compatible --safe #-}

module StdlibExt.Data.Nat.Properties where

open import Data.Nat
open import Data.Nat.Properties public
open ≤-Reasoning

n<n+1 : ∀ {n} → n < n + 1
n<n+1 {n} = m<m+n n (s≤s z≤n)

∸-monoˡ-< : ∀ {m n o} → m < o → n ≤ m → m ∸ n < o ∸ n
∸-monoˡ-< {m}     {zero}  {o}     m<o       n≤m       = m<o
∸-monoˡ-< {suc m} {suc n} {suc o} (s≤s m<o) (s≤s n≤m) = ∸-monoˡ-< m<o n≤m

m<1+n⇒m≤n : ∀ {m n} → m < suc n → m ≤ n
m<1+n⇒m≤n (s≤s m≤n) = m≤n

m<m+n+1 : ∀ m n → m < m + n + 1
m<m+n+1 m n = begin
  suc m       ≤⟨ s≤s (m≤m+n m n) ⟩
  suc (m + n) ≡⟨ +-comm 1 (m + n) ⟩
  m + n + 1   ∎
