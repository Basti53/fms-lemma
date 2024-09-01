{-# OPTIONS --rewriting #-}
module Inverses where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _/_; _^_; _<_; _≤_; z<s; z≤n; s≤s)
open import Data.Nat.Properties using (+-identityʳ; n∸n≡0; +-∸-assoc; +-mono-<)
open import Data.Nat.DivMod using (n/n≡1)
open import Data.Bool.Base using (Bool; true; false)
open import Agda.Builtin.Nat using (div-helper)
-- open import Axiom.Extensionality.Propositional using (Extensionality)
open import Definitions

postulate
  extensionality : ∀ {A B : Set} {f g : A -> B} -> (∀ (x : A) -> f x ≡ g x) -> f ≡ g
  -- TODO: Write this using imports.

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

𝑓⁻¹𝑓n : ∀ (φ : ℕ -> Bool) (n : ℕ) -> 𝑓⁻¹ (𝑓 φ) n ≡ φ n
𝑓⁻¹𝑓n φ zero with φ zero
... | true = refl
... | false = refl
𝑓⁻¹𝑓n φ (suc n) with φ (suc n)
... | true rewrite helper₁ (2 ^ (suc n)) (0<2^n (suc n)) = refl
... | false = refl

𝑓⁻¹𝑓 : ∀ (φ : ℕ -> Bool) -> 𝑓⁻¹ (𝑓 φ) ≡ φ
𝑓⁻¹𝑓 φ = extensionality (𝑓⁻¹𝑓n φ)

𝑓𝑓⁻¹n : ∀ (f : ℕ -> ℕ) (n : ℕ) -> ℱ f -> 𝑓 (𝑓⁻¹ f) n ≡ f n
𝑓𝑓⁻¹n .(𝑓 φ) zero (∈ℱ φ refl) = refl
𝑓𝑓⁻¹n .(𝑓 φ) (suc n) (∈ℱ φ refl) with φ n
... | true rewrite helper₁ (2 ^ n) (0<2^n n) | 𝑓⁻¹𝑓 φ = refl
... | false rewrite 𝑓⁻¹𝑓 φ = refl

𝑓𝑓⁻¹ : ∀ (f : ℕ -> ℕ) -> ℱ f -> 𝑓 (𝑓⁻¹ f) ≡ f
𝑓𝑓⁻¹ f ℱf = extensionality (λ n -> 𝑓𝑓⁻¹n f n ℱf)
