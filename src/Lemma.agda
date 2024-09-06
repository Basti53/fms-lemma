{-# OPTIONS --rewriting #-} -- Can I get rid of this?
module Lemma where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _<_; _≤_; z<s; s<s; z≤n; s≤s; _≤?_)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Properties using (+-identityʳ)
open import Function using (_↔_; mk↔ₛ′; StrictlyInverseˡ; StrictlyInverseʳ)
open import Data.Product using (Σ; _,_; proj₁; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Definitions
open import Bounds
open import Inverses

lemma-1 : (ℕ -> Bool) ↔ (∃[ f ] (ℱ f))
lemma-1 = mk↔ₛ′ (λ φ -> 𝑓 φ , ∈ℱ φ refl) (λ (f , pf) -> 𝑓⁻¹ f) {!!} (λ φ -> 𝑓⁻¹𝑓 φ)

lemma-2 : ∀ {n : ℕ} {f : ℕ -> ℕ} -> ℱ f -> f n < 2 ^ n
lemma-2 {n} {.(𝑓 φ)} (∈ℱ φ refl) = lemma-2-1 n φ

helper : ∀ (m n : ℕ) -> m ≤ n -> m ≡ n ⊎ m < n
helper zero zero m≤n = inj₁ refl
helper zero (suc n) m≤n = inj₂ z<s
helper (suc m) (suc n) (s≤s m≤n) with helper m n m≤n
... | inj₁ refl = inj₁ refl
... | inj₂ m<n = inj₂ (s<s m<n)

m-Induction : ∀ (P : ℕ -> Set) (m : ℕ) -> ((p : ℕ) -> P p -> P (suc p)) -> P m -> ∀ (n : ℕ) -> m ≤ n -> P n
m-Induction P zero Pp->Psp Pm zero z≤n = Pm
m-Induction P zero Pp->Psp Pm (suc n) z≤n = Pp->Psp n (m-Induction P zero Pp->Psp Pm n z≤n)
m-Induction P (suc m) Pp->Psp Pm (suc n) (s≤s m≤n) with helper m n m≤n
... | inj₁ m≡n rewrite sym m≡n = Pm
... | inj₂ m<n = Pp->Psp n (m-Induction P (suc m) Pp->Psp Pm n m<n)

lemma-3-2 : ∀ (φ φ' : ℕ -> Bool) (n : ℕ) -> 𝑓 φ n ≢ 𝑓 φ' n -> 𝑓 φ (suc n) ≢ 𝑓 φ' (suc n)
lemma-3-2 φ φ' zero 𝑓φ≢𝑓φ' with φ 0 | φ' 0
... | false | false = λ _ -> 𝑓φ≢𝑓φ' refl
... | false | true = λ()
... | true | false = λ()
... | true | true = λ _ -> 𝑓φ≢𝑓φ' refl
lemma-3-2 φ φ' (suc n) 𝑓φ≢𝑓φ' with φ (suc n) | φ' (suc n)
... | false | false = 𝑓φ≢𝑓φ'
... | false | true = {!!}
... | true | false = {!!}
... | true | true = {!!}

lemma-3-1 : ∀ (φ φ' : ℕ -> Bool) (m : ℕ) -> 𝑓 φ m ≢ 𝑓 φ' m -> ∀ (n : ℕ) -> m ≤ n ->  𝑓 φ n ≢ 𝑓 φ' n
lemma-3-1 φ φ' m = m-Induction (λ p ->  𝑓 φ p ≢ 𝑓 φ' p) m (lemma-3-2 φ φ')

lemma-3 : ∀ {f g : ℕ -> ℕ} -> ℱ f -> ℱ g -> ∃[ m ] f m ≢ g m -> ∃[ m ] (∀ (n : ℕ) -> m ≤ n -> f n ≢ g n)
lemma-3 {.(𝑓 φ)} {.(𝑓 φ')} (∈ℱ φ refl) (∈ℱ φ' refl) (m , fn≢gn) = m , lemma-3-1 φ φ' m fn≢gn
