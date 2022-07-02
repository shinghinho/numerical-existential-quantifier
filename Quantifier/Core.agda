{-# OPTIONS --without-K --safe #-}

module Quantifier.Core where

open import Data.Maybe public
open import Data.Empty
open import Data.Product
open import Data.Vec using (Vec) renaming ([] to v[]; _∷_ to _v∷_; length to vlength; lookup to vlookup)
open import Data.List using (List) renaming ([] to l[]; _∷_ to _l∷_; length to llength)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _≤_; z≤n; s≤s) public
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc) public
open import Function public
open import Level renaming (zero to lzero; suc to lsuc; _⊔_ to _⊔ˡ_) public
open import Relation.Binary.PropositionalEquality public
open Relation.Binary.PropositionalEquality.≡-Reasoning public

private
  variable
    𝓁 𝓁′ 𝓁″ 𝓁‴ : Level
    A : Set 𝓁
    B : Set 𝓁′
    C : Set 𝓁″
    D : Set 𝓁‴
    i j : A

-- A unique indexing of `A'-many Bs. (Commutativity witnessed by `isUnique')
--       A  ----- index ------> B
--       |         ||           |
--  just |         || is-unique | indexed-by
--       |         ||           |
--       V         ||           V
--   Maybe A =============== Maybe A
infixr 1 _→!_
record _→!_ (A : Set 𝓁) (B : Set 𝓁′) : Set (𝓁 ⊔ˡ 𝓁′) where
  field
    index : A → B
    indexed-by : B → Maybe A
    is-unique : ∀ (i : A) → indexed-by (index i) ≡ just i
open _→!_ public

index-injective : (f : A →! B) → index f i ≡ index f j → i ≡ j
index-injective {i = i} {j = j} f p = just-injective just-i≡just-j
  where
    just-injective : {A : Set 𝓁″} {a b : A} → just a ≡ just b → a ≡ b
    just-injective refl = refl
    just-i≡just-j : just i ≡ just j
    just-i≡just-j =
         just i
       ≡⟨ sym (is-unique f i) ⟩
         indexed-by f (index f i)
       ≡⟨ cong (indexed-by f) p ⟩
         indexed-by f (index f j)
       ≡⟨ is-unique f j ⟩
         just j
       ∎

index-resp-≢ : (f : A →! B) → i ≢ j → index f i ≢ index f j
index-resp-≢ f neq = neq ∘ index-injective f

id! : A →! A
index id! = id
indexed-by id! = just
is-unique id! i = refl

⊥! : ⊥ →! A
index ⊥! ()
indexed-by ⊥! = const nothing
is-unique ⊥! ()

_∘!_ : (B →! C)
     → (A →! B)
     → A →! C
index (g ∘! f) x = index g (index f x)
indexed-by (g ∘! f) z = do y ← indexed-by g z
                           x ← indexed-by f y
                           just x
is-unique (g ∘! f) x =
    indexed-by (g ∘! f) (index (g ∘! f) x)
  ≡⟨ refl ⟩
    indexed-by (g ∘! f) (index g (index f x))
  ≡⟨ refl ⟩
    (indexed-by g (index g (index f x)) >>= λ y →
     indexed-by f y >>= just)
  ≡⟨ cong (λ α → α >>= λ y → indexed-by f y >>= just) (is-unique g (index f x)) ⟩
    (just (index f x) >>= λ y →
     indexed-by f y >>= just)
  ≡⟨ refl ⟩
    (indexed-by f (index f x) >>= just)
  ≡⟨ cong (_>>= just) (is-unique f x) ⟩
    just x
  ∎

-- Unique indexing can be lifted over product
_×!_ : (f : A →! C)
     → (g : B →! D)
     → A × B →! C × D
index (f ×! g) (x , y) = index f x , index g y
indexed-by (f ×! g) (x , y) = do p ← indexed-by f x
                                 q ← indexed-by g y
                                 just (p , q)
is-unique (f ×! g) (x , y) =
    indexed-by (f ×! g) (index (f ×! g) (x , y))
  ≡⟨ refl ⟩
    indexed-by (f ×! g) (index f x , index g y)
  ≡⟨ refl ⟩
    (indexed-by f (index f x) >>= λ p →
     indexed-by g (index g y) >>= λ q →
     just (p , q))
  ≡⟨ cong (λ α → α >>= λ p → indexed-by g (index g y) >>= λ q → just (p , q)) (is-unique f x) ⟩
    (just x >>= λ p →
     indexed-by g (index g y) >>= λ q →
     just (p , q))
  ≡⟨ cong (λ α → just x >>= λ p → α >>= λ q → just (p , q)) (is-unique g y) ⟩
    (just x >>= λ p → just y >>= λ q → just (p , q))
  ≡⟨ refl ⟩
    just (x , y)
  ∎

Unique : Set 𝓁 → ℕ → Set _
Unique A n = Fin n →! A

unique-0 : Unique A 0
index unique-0 ()
indexed-by unique-0 = const nothing
is-unique unique-0 ()

pointed : {n : ℕ} → Unique A (suc n) → A
pointed = flip index fzero

fin-surj : {n : ℕ} → Fin (suc n) → Maybe (Fin n)
fin-surj fzero = nothing
fin-surj (fsuc x) = just x

-- Having (1 + n) unique elements => having n unique elements
pred! : {n : ℕ} → Unique A (suc n) → Unique A n
index (pred! f) x = index f (fsuc x)
indexed-by (pred! f) x = do i ← indexed-by f x
                            fin-surj i
is-unique (pred! {n = suc m} f) i =
    (indexed-by f (index f (fsuc i)) >>= fin-surj)
  ≡⟨ cong (_>>= fin-surj) (is-unique f (fsuc i)) ⟩
    (just (fsuc i) >>= fin-surj)
  ≡⟨ refl ⟩
    just i
  ∎

-- Reify the element to a unique list
list! : {n : ℕ} → Unique A n → List A
list! {n = zero} f = l[]
list! {n = suc n} f = index f fzero l∷ list! {n = n} (pred! f)

list!-length : {n : ℕ} → (f : Unique A n) → llength (list! f) ≡ n
list!-length {n = zero} f = refl
list!-length {n = suc n} f =
    llength (index f fzero l∷ list! (pred! f))
  ≡⟨ refl ⟩
    suc (llength (list! (pred! f)))
  ≡⟨ cong suc (list!-length {n = n} (pred! f)) ⟩
    suc n
  ∎

vec! : {n : ℕ} → Unique A n → Vec A n
vec! {n = zero} f = v[]
vec! {n = suc n} f = index f fzero v∷ vec! (pred! f)

vec!-preserves-index : {n : ℕ} (f : Unique A n)
                     → {i : Fin n}
                     → vlookup (vec! f) i ≡ index f i
vec!-preserves-index f {i = fzero} = refl
vec!-preserves-index f {i = fsuc i} = vec!-preserves-index (pred! f) {i = i}

vec!-has-unique-elems : {n : ℕ} {i j : Fin n}
                      → (f : Unique A n)
                      → (i ≢ j)
                      → (vlookup (vec! f) i ≢ vlookup (vec! f) j)
vec!-has-unique-elems {i = i} {j = j} f neq eq = neq (index-injective f lemma)
  where
    lemma : index f i ≡ index f j
    lemma =
        index f i
      ≡⟨ sym (vec!-preserves-index f) ⟩
        vlookup (vec! f) i
      ≡⟨ eq ⟩
        vlookup (vec! f) j
      ≡⟨ vec!-preserves-index f {i = j} ⟩
        index f j
      ∎

vlookup∘vec-injective : {n : ℕ} {i j : Fin n}
                      → (f : Unique A n)
                      → (vlookup (vec! f) i ≡ vlookup (vec! f) j)
                      → i ≡ j
vlookup∘vec-injective {i = i} {j = j} f eq = index-injective f lemma
  where
    lemma : index f i ≡ index f j
    lemma =
        index f i
      ≡⟨ sym (vec!-preserves-index f) ⟩
        vlookup (vec! f) i
      ≡⟨ eq ⟩
        vlookup (vec! f) j
      ≡⟨ vec!-preserves-index f {i = j} ⟩
        index f j
      ∎

record UVec (A : Set 𝓁) (n : ℕ) : Set 𝓁 where
  field
    carrier : Vec A n
    is-unique : {i j : Fin n} → i ≢ j → vlookup carrier i ≢ vlookup carrier j
    is-injective : {i j : Fin n} → vlookup carrier i ≡ vlookup carrier j → i ≡ j
open UVec public

→!-to-uvec : {n : ℕ} → Unique A n → UVec A n
carrier (→!-to-uvec f) = vec! f
is-unique (→!-to-uvec f) = vec!-has-unique-elems f
is-injective (→!-to-uvec f) = vlookup∘vec-injective f

uvlookup : {n : ℕ} → UVec A n → Fin n → A
uvlookup = vlookup ∘ carrier

_∈_ : B → (A →! B) → Set _
_∈_ {A = A} x f = Σ A (λ i → x ≡ index f i)
