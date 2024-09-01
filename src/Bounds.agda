{-# OPTIONS --allow-unsolved-metas #-}
module Bounds where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _<_; _≤_; z<s; s<s; z≤n; s≤s)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Properties using (+-identityʳ; +-monoʳ-<; +-monoʳ-≤; +-mono-≤)
open import Definitions

lemma-2-3 : ∀ (n : ℕ) -> 𝑓 (λ _ -> true) n < 2 ^ n
lemma-2-3 zero = z<s
lemma-2-3 (suc n) rewrite +-identityʳ (2 ^ n) = +-monoʳ-< (2 ^ n) (lemma-2-3 n)

lemma-2-2 : ∀ (n : ℕ) (φ : ℕ -> Bool) -> 𝑓 φ n ≤ 𝑓 (λ _ -> true) n
lemma-2-2 zero φ = z≤n
lemma-2-2 (suc n) φ with φ n
... | true rewrite +-identityʳ (2 ^ n) = +-monoʳ-≤ (2 ^ n) (lemma-2-2 n φ)
... | false rewrite +-identityʳ (2 ^ n) = +-mono-≤ (0≤2^ n) (lemma-2-2 n φ)
  where
    0≤2^ : ∀ (n : ℕ) -> zero ≤ 2 ^ n
    0≤2^ n = z≤n

lemma-2-1 : ∀ (n : ℕ) (φ : ℕ -> Bool) -> 𝑓 φ n < 2 ^ n
lemma-2-1 n φ = {!!}
