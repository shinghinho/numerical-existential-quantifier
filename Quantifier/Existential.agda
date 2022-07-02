{-# OPTIONS --without-K --safe #-}

module Quantifier.Existential where

open import Quantifier.Core

private
  variable
    𝓁 𝓁′ 𝓁″ 𝓁‴ 𝓁⁗ : Level
    A : Set 𝓁
    B : Set 𝓁′
    C : Set 𝓁″
    D : Set 𝓁‴
    P : A → Set 𝓁⁗
    m n : ℕ

-- There are at least n elements such that P holds
record ∃≥_[_] (n : ℕ) (A : Set 𝓁) (P : A → Set 𝓁′) : Set (𝓁 ⊔ˡ 𝓁′) where 
  field
    elements : Unique A n
    holds : (i : Fin n) → P (index elements i)
open ∃≥_[_] public

pred∃≥ : ∃≥ (suc n) [ A ] P → ∃≥ n [ A ] P
elements (pred∃≥ f) = pred! (elements f)
holds (pred∃≥ xs) i = holds xs (fsuc i)

∃≥0 : ∃≥ 0 [ A ] P
elements ∃≥0 = unique-0
holds ∃≥0 ()

-- Countably infinite
CountablyInfinitelyMany : Set 𝓁 → Set 𝓁
CountablyInfinitelyMany A = ℕ →! A

-- There are (countably) infinitely many elements such that P holds
record ∃∞[_] (A : Set 𝓁) (P : A → Set 𝓁′) : Set (𝓁 ⊔ˡ 𝓁′) where
  field
    elements : CountablyInfinitelyMany A
    holds : (i : ℕ) → P (index elements i)
open ∃∞[_] public

-- Example: there are countably infinitely many even numbers
module Example where
  data even : ℕ → Set where
    zero : even 0
    suc² : even n → even (suc (suc n))

  double : ℕ → ℕ
  double zero = zero
  double (suc x) = suc (suc (double x))

  halve? : ℕ → Maybe ℕ
  halve? zero = just zero
  halve? (suc zero) = nothing
  halve? (suc (suc x)) = do y ← halve? x
                            just (suc y)

  eq : (n : ℕ) → halve? (double n) ≡ just n
  eq zero = refl
  eq (suc zero) = refl
  eq (suc (suc n)) =
      (halve? (double n) >>= just ∘ suc >>= just ∘ suc)
    ≡⟨ cong (λ α → α >>= just ∘ suc >>= just ∘ suc) (eq n) ⟩
      (just n >>= just ∘ suc >>= just ∘ suc)
    ≡⟨ refl ⟩
      just (suc (suc n))
    ∎

  double-index : CountablyInfinitelyMany ℕ
  index double-index = double
  indexed-by double-index = halve?
  is-unique double-index = eq

  double-implies-even : (n : ℕ) → even (double n)
  double-implies-even zero = zero
  double-implies-even (suc n) = suc² (double-implies-even n)

  -- Main theorem
  inf-evens : ∃∞[ ℕ ] even
  elements inf-evens = double-index
  holds inf-evens = double-implies-even

∃≥-ind : ((n : ℕ) → ∃≥ n [ A ] P → ∃≥ suc n [ A ] P)
       → (m : ℕ)
       → ∃≥ m [ A ] P
∃≥-ind f zero = ∃≥0
∃≥-ind f (suc m) = f m (∃≥-ind f m)

-- There are exactly n elements such that P holds
record ∃!_[_] (n : ℕ) (A : Set 𝓁) (P : A → Set 𝓁′) : Set (𝓁 ⊔ˡ 𝓁′) where
  field
    exists : ∃≥ n [ A ] P
    exact : (a : A) → P a → a ∈ elements exists
open ∃!_[_] public

∃!⇒∃≥ : ∃! n [ A ] P → ∃≥ n [ A ] P
∃!⇒∃≥ f = exists f
