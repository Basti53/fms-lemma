module Definitions where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _<_)
open import Data.Bool.Base using (Bool; true; false)

boolToNat : Bool -> ℕ
boolToNat false = zero
boolToNat true = 1

𝑓 : (ℕ -> Bool) -> ℕ -> ℕ
𝑓 φ zero = zero
𝑓 φ (suc n) = boolToNat (φ n) * (2 ^ n) + (𝑓 φ n)

data ℱ (f : ℕ -> ℕ) : Set where
  ∈ℱ : (φ : ℕ -> Bool) -> (f ≡ 𝑓 φ) -> ℱ f
