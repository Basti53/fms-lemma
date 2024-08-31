{-# OPTIONS --rewriting #-}
module Inverses where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _/_; _^_; _<_; _≤_; z<s; z≤n; s≤s)
open import Data.Nat.Properties using (+-identityʳ; n∸n≡0; +-∸-assoc; +-mono-<)
open import Data.Nat.DivMod using (n/n≡1)
open import Data.Bool.Base using (Bool; true; false)
open import Agda.Builtin.Nat using (div-helper)
open import Definitions

{-# REWRITE +-identityʳ n∸n≡0 #-}

n≤n : ∀ {n : ℕ} -> n ≤ n
n≤n {zero} = z≤n
n≤n {suc n} = s≤s n≤n

m+n∸n≡m : ∀ (m n : ℕ) -> m + n ∸ n ≡ m
m+n∸n≡m m n = +-∸-assoc m {n} {n} n≤n 

{-# REWRITE m+n∸n≡m #-}

0<2^n : ∀ (n : ℕ) -> 0 < 2 ^ n
0<2^n zero = z<s
0<2^n (suc n) = +-mono-< (0<2^n n) (0<2^n n)

helper₁ : ∀ (n : ℕ) -> zero < n -> div-helper 0 (n ∸ 1) n (n ∸ 1) ≡ 1
helper₁ .(suc n) (z<s {n}) = n/n≡1 (suc n)

𝑓⁻¹𝑓 : ∀ (n : ℕ) (φ : ℕ -> Bool) -> 𝑓⁻¹ (𝑓 φ) n ≡ φ n
𝑓⁻¹𝑓 zero φ with φ zero
... | true = refl
... | false = refl
𝑓⁻¹𝑓 (suc n) φ with φ (suc n)
... | true rewrite helper₁ (2 ^ (suc n)) (0<2^n (suc n)) = refl
... | false = refl

𝑓𝑓⁻¹ : ∀ (n : ℕ) (f : ℕ -> ℕ) -> ℱ f -> 𝑓 (𝑓⁻¹ f) n ≡ f n
𝑓𝑓⁻¹ n f ℱf = {!!}
