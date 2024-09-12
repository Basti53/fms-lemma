{-# OPTIONS --rewriting #-}
module Lemma where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Agda.Builtin.Nat using (div-helper)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.DivMod using (n/n≡1)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; ∃; ∃-syntax)
open import Data.Empty using (⊥)

{-# REWRITE +-identityʳ n∸n≡0 m+n∸n≡m #-}

postulate
  extensionality : ∀ {A B : Set} {f g : A -> B} -> (∀ (x : A) -> f x ≡ g x) -> f ≡ g

boolToNat : Bool -> ℕ
boolToNat false = zero
boolToNat true = 1

𝑓 : (ℕ -> Bool) -> ℕ -> ℕ
𝑓 φ zero = zero
𝑓 φ (suc n) = boolToNat (φ n) * (2 ^ n) + (𝑓 φ n)

data ℱ (f : ℕ -> ℕ) : Set where
  ∈ℱ : (φ : ℕ -> Bool) -> (f ≡ 𝑓 φ) -> ℱ f

𝑓⁻¹ : (ℕ -> ℕ) -> ℕ -> Bool
𝑓⁻¹ f n with (f (suc n) ∸ f n) / suc (2 ^ n ∸ 1)
... | zero = false
... | suc n = true

0<2^n : ∀ (n : ℕ) -> 0 < 2 ^ n
0<2^n zero = z<s
0<2^n (suc n) = +-mono-< (0<2^n n) (0<2^n n)

div-helper≡ : ∀ (n : ℕ) -> zero < n -> div-helper 0 (n ∸ 1) n (n ∸ 1) ≡ 1
div-helper≡ .(suc n) (z<s {n}) = n/n≡1 (suc n)

𝑓⁻¹𝑓n : ∀ (φ : ℕ -> Bool) (n : ℕ) -> 𝑓⁻¹ (𝑓 φ) n ≡ φ n
𝑓⁻¹𝑓n φ zero with φ zero
... | true = refl
... | false = refl
𝑓⁻¹𝑓n φ (suc n) with φ (suc n)
... | true rewrite div-helper≡ (2 ^ (suc n)) (0<2^n (suc n)) = refl
... | false = refl

𝑓⁻¹𝑓 : ∀ (φ : ℕ -> Bool) -> 𝑓⁻¹ (𝑓 φ) ≡ φ
𝑓⁻¹𝑓 φ = extensionality (𝑓⁻¹𝑓n φ)

𝑓𝑓⁻¹n : ∀ (f : ℕ -> ℕ) (n : ℕ) -> ℱ f -> 𝑓 (𝑓⁻¹ f) n ≡ f n
𝑓𝑓⁻¹n .(𝑓 φ) zero (∈ℱ φ refl) = refl
𝑓𝑓⁻¹n .(𝑓 φ) (suc n) (∈ℱ φ refl) with φ n
... | true rewrite div-helper≡ (2 ^ n) (0<2^n n) | 𝑓⁻¹𝑓 φ = refl
... | false rewrite 𝑓⁻¹𝑓 φ = refl

𝑓𝑓⁻¹ : ∀ (f : ℕ -> ℕ) -> ℱ f -> 𝑓 (𝑓⁻¹ f) ≡ f
𝑓𝑓⁻¹ f ℱf = extensionality (λ n -> 𝑓𝑓⁻¹n f n ℱf)

𝑓λ_->true<2^n : ∀ (n : ℕ) -> 𝑓 (λ _ -> true) n < 2 ^ n
𝑓λ_->true<2^n zero = z<s
𝑓λ_->true<2^n (suc n) = +-monoʳ-< (2 ^ n) (𝑓λ_->true<2^n n)

𝑓φ≤𝑓λ_->true : ∀ (n : ℕ) (φ : ℕ -> Bool) -> 𝑓 φ n ≤ 𝑓 (λ _ -> true) n
𝑓φ≤𝑓λ_->true zero φ = z≤n
𝑓φ≤𝑓λ_->true (suc n) φ with φ n
... | true = +-monoʳ-≤ (2 ^ n) (𝑓φ≤𝑓λ_->true n φ)
... | false = +-mono-≤ (0≤2^ n) (𝑓φ≤𝑓λ_->true n φ)
  where
    0≤2^ : ∀ (n : ℕ) -> zero ≤ 2 ^ n
    0≤2^ n = z≤n

≤→≡⊎< : ∀ (m n : ℕ) -> m ≤ n -> m ≡ n ⊎ m < n
≤→≡⊎< zero zero m≤n = inj₁ refl
≤→≡⊎< zero (suc n) m≤n = inj₂ z<s
≤→≡⊎< (suc m) (suc n) (s≤s m≤n) with ≤→≡⊎< m n m≤n
... | inj₁ refl = inj₁ refl
... | inj₂ m<n = inj₂ (s<s m<n)

≤<→< : ∀ (m n p : ℕ) -> m ≤ n -> n < p -> m < p
≤<→< m n p m≤n n<p with ≤→≡⊎< m n m≤n
... | inj₁ refl = n<p
... | inj₂ _ = ≤-trans (s≤s m≤n) n<p

𝑓φn<2^n : ∀ (n : ℕ) (φ : ℕ -> Bool) -> 𝑓 φ n < 2 ^ n
𝑓φn<2^n n φ = ≤<→< (𝑓 φ n) (𝑓 (λ _ → true) n) (2 ^ n) (𝑓φ≤𝑓λ_->true n φ) (𝑓λ_->true<2^n n)

lemma-2 : ∀ {n : ℕ} {f : ℕ -> ℕ} -> ℱ f -> f n < 2 ^ n
lemma-2 {n} {.(𝑓 φ)} (∈ℱ φ refl) = 𝑓φn<2^n n φ

m-Induction : ∀ (P : ℕ -> Set) (m : ℕ) -> ((p : ℕ) -> P p -> P (suc p)) -> P m -> ∀ (n : ℕ) -> m ≤ n -> P n
m-Induction P zero Pp->Psp Pm zero z≤n = Pm
m-Induction P zero Pp->Psp Pm (suc n) z≤n = Pp->Psp n (m-Induction P zero Pp->Psp Pm n z≤n)
m-Induction P (suc m) Pp->Psp Pm (suc n) (s≤s m≤n) with ≤→≡⊎< m n m≤n
... | inj₁ m≡n rewrite sym m≡n = Pm
... | inj₂ m<n = Pp->Psp n (m-Induction P (suc m) Pp->Psp Pm n m<n)

n<m->n≡m+k->⊥ : ∀ (n m k : ℕ) -> n < m -> n ≡ m + k -> ⊥
n<m->n≡m+k->⊥ n m k n<m n≡m+k = {!!}

𝑓φn≢𝑓φ'n->𝑓φsn≢𝑓φ'sn : ∀ (φ φ' : ℕ -> Bool) (n : ℕ) -> 𝑓 φ n ≢ 𝑓 φ' n -> 𝑓 φ (suc n) ≢ 𝑓 φ' (suc n)
𝑓φn≢𝑓φ'n->𝑓φsn≢𝑓φ'sn φ φ' zero 𝑓φ≢𝑓φ' with φ 0 | φ' 0
... | false | false = λ _ -> 𝑓φ≢𝑓φ' refl
... | false | true = λ()
... | true | false = λ()
... | true | true = λ _ -> 𝑓φ≢𝑓φ' refl
𝑓φn≢𝑓φ'n->𝑓φsn≢𝑓φ'sn φ φ' (suc n) 𝑓φ≢𝑓φ' with φ (suc n) | φ' (suc n)
... | false | false = 𝑓φ≢𝑓φ'
... | false | true = λ x -> n<m->n≡m+k->⊥ (𝑓 φ (suc n)) (2 ^ (suc n)) (𝑓 φ' (suc n)) (𝑓φn<2^n (suc n) φ) x
... | true | false = λ x -> n<m->n≡m+k->⊥ (𝑓 φ' (suc n)) (2 ^ (suc n)) (𝑓 φ (suc n)) (𝑓φn<2^n (suc n) φ') (sym x)
... | true | true = λ x -> 𝑓φ≢𝑓φ' (+-cancelˡ-≡ (2 ^ (suc n)) (𝑓 φ (suc n)) (𝑓 φ' (suc n))  x)

lemma-3' : ∀ (φ φ' : ℕ -> Bool) (m : ℕ) -> 𝑓 φ m ≢ 𝑓 φ' m -> ∀ (n : ℕ) -> m ≤ n ->  𝑓 φ n ≢ 𝑓 φ' n
lemma-3' φ φ' m = m-Induction (λ p ->  𝑓 φ p ≢ 𝑓 φ' p) m (𝑓φn≢𝑓φ'n->𝑓φsn≢𝑓φ'sn φ φ')

lemma-3 : ∀ {f g : ℕ -> ℕ} -> ℱ f -> ℱ g -> ∃[ m ] f m ≢ g m -> ∃[ m ] (∀ (n : ℕ) -> m ≤ n -> f n ≢ g n)
lemma-3 {.(𝑓 φ)} {.(𝑓 φ')} (∈ℱ φ refl) (∈ℱ φ' refl) (m , fn≢gn) = m , lemma-3' φ φ' m fn≢gn
