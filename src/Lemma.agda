{-# OPTIONS --rewriting #-} -- Can I get rid of this?
module Lemma where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _<_; _≤_; z<s; s<s; z≤n; s≤s)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Properties using (+-identityʳ)
open import Function using (_↔_; mk↔ₛ′; StrictlyInverseˡ; StrictlyInverseʳ)
open import Data.Product using (Σ; _,_; proj₁; ∃; ∃-syntax)
open import Definitions
open import Bounds
open import Inverses

lemma-1 : (ℕ -> Bool) ↔ (∃[ f ] (ℱ f))
lemma-1 = mk↔ₛ′ (λ φ -> 𝑓 φ , ∈ℱ φ refl) (λ (f , pf) -> 𝑓⁻¹ f) {!!} (λ φ -> 𝑓⁻¹𝑓 φ)

lemma-2 : ∀ {n : ℕ} {f : ℕ -> ℕ} -> ℱ f -> f n < 2 ^ n
lemma-2 {n} {.(𝑓 φ)} (∈ℱ φ refl) = lemma-2-1 n φ

lemma-3-2 : ∀ (φ φ' : ℕ -> Bool) (n : ℕ) -> 𝑓 φ n ≢ 𝑓 φ' n -> 𝑓 φ (suc n) ≢ 𝑓 φ' (suc n)
lemma-3-2 φ φ' n 𝑓φ≢𝑓φ' = {!!}

lemma-3-1 : ∀ (φ φ' : ℕ -> Bool) (m : ℕ) -> 𝑓 φ m ≢ 𝑓 φ' m -> ∀ (n : ℕ) -> m < n ->  𝑓 φ n ≢ 𝑓 φ' n
lemma-3-1 φ φ' zero 𝑓φ≢𝑓φ' .1 (s<s {.0} {zero} m<n) = {!!}
lemma-3-1 φ φ' zero 𝑓φ≢𝑓φ' .(suc (suc n)) (s<s {.0} {suc n} m<n) = {!!}
lemma-3-1 φ φ' (suc m) 𝑓φ≢𝑓φ' .(suc n) (s<s {.(suc m)} {n} m<n) = {!!}

lemma-3 : ∀ {f g : ℕ -> ℕ} -> ℱ f -> ℱ g -> ∃[ m ] f m ≢ g m -> ∃[ m ] (∀ (n : ℕ) -> m < n -> f n ≢ g n)
lemma-3 {.(𝑓 φ)} {.(𝑓 φ')} (∈ℱ φ refl) (∈ℱ φ' refl) (m , fn≢gn) = m , lemma-3-1 φ φ' m fn≢gn
