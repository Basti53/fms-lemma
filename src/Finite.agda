module Finite where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _<_; _≤_; z<s; s<s; z≤n; s≤s)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Product using (Σ; _,_; proj₁; ∃; ∃-syntax)
open import Definitions

postulate
  extensionality : ∀ {A B : Set} {f g : A -> B} -> (∀ (x : A) -> f x ≡ g x) -> f ≡ g

lemma3-1 : ∀ {f g : ℕ -> ℕ} -> f ≢ g -> ∃[ n ] (f n ≢ g n)
lemma3-1 {f} {g} f≢g = {!!} -- Is this possible?
