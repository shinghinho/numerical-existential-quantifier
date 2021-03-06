{-# OPTIONS --without-K --safe #-}

module Quantifier.Existential where

open import Quantifier.Core

private
  variable
    π πβ² πβ³ πβ΄ πβ : Level
    A : Set π
    B : Set πβ²
    C : Set πβ³
    D : Set πβ΄
    P : A β Set πβ
    m n : β

-- There are at least n elements such that P holds
record ββ₯_[_] (n : β) (A : Set π) (P : A β Set πβ²) : Set (π βΛ‘ πβ²) where 
  field
    elements : Unique A n
    holds : (i : Fin n) β P (index elements i)
open ββ₯_[_] public

predββ₯ : ββ₯ (suc n) [ A ] P β ββ₯ n [ A ] P
elements (predββ₯ f) = pred! (elements f)
holds (predββ₯ xs) i = holds xs (fsuc i)

ββ₯0 : ββ₯ 0 [ A ] P
elements ββ₯0 = unique-0
holds ββ₯0 ()

-- Countably infinite
CountablyInfinitelyMany : Set π β Set π
CountablyInfinitelyMany A = β β! A

-- There are (countably) infinitely many elements such that P holds
record ββ[_] (A : Set π) (P : A β Set πβ²) : Set (π βΛ‘ πβ²) where
  field
    elements : CountablyInfinitelyMany A
    holds : (i : β) β P (index elements i)
open ββ[_] public

-- Example: there are countably infinitely many even numbers
module Example where
  data even : β β Set where
    zero : even 0
    sucΒ² : even n β even (suc (suc n))

  double : β β β
  double zero = zero
  double (suc x) = suc (suc (double x))

  halve? : β β Maybe β
  halve? zero = just zero
  halve? (suc zero) = nothing
  halve? (suc (suc x)) = do y β halve? x
                            just (suc y)

  eq : (n : β) β halve? (double n) β‘ just n
  eq zero = refl
  eq (suc zero) = refl
  eq (suc (suc n)) =
      (halve? (double n) >>= just β suc >>= just β suc)
    β‘β¨ cong (Ξ» Ξ± β Ξ± >>= just β suc >>= just β suc) (eq n) β©
      (just n >>= just β suc >>= just β suc)
    β‘β¨ refl β©
      just (suc (suc n))
    β

  double-index : CountablyInfinitelyMany β
  index double-index = double
  indexed-by double-index = halve?
  is-unique double-index = eq

  double-implies-even : (n : β) β even (double n)
  double-implies-even zero = zero
  double-implies-even (suc n) = sucΒ² (double-implies-even n)

  -- Main theorem
  inf-evens : ββ[ β ] even
  elements inf-evens = double-index
  holds inf-evens = double-implies-even

ββ₯-ind : ((n : β) β ββ₯ n [ A ] P β ββ₯ suc n [ A ] P)
       β (m : β)
       β ββ₯ m [ A ] P
ββ₯-ind f zero = ββ₯0
ββ₯-ind f (suc m) = f m (ββ₯-ind f m)

-- There are exactly n elements such that P holds
record β!_[_] (n : β) (A : Set π) (P : A β Set πβ²) : Set (π βΛ‘ πβ²) where
  field
    exists : ββ₯ n [ A ] P
    exact : (a : A) β P a β a β elements exists
open β!_[_] public

β!βββ₯ : β! n [ A ] P β ββ₯ n [ A ] P
β!βββ₯ f = exists f
