{-# OPTIONS --cubical --guardedness #-}
-- Boolean comparisons on ℕ, their reflection lemmas, and the Boolean
-- eliminators that let a proof follow an `if_then_else_` without `with`
-- (which would destroy the lexicographic descent a termination check needs).
module NatBool where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path using (inspect; [_]ᵢ)
open import Cubical.Data.Sigma.Base using (_×_)
open import Cubical.Data.Sum.Base using (_⊎_)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (_≤_; _<_; ≤Dec; <Dec; <-weaken; splitℕ-<; splitℕ-≤)
open import Cubical.Data.Bool using (Bool; true; false; Bool→Type; Dec→Bool; _and_; if_then_else_)
open import Cubical.Data.Bool.Properties using (true≢false; false≢true; Dec→DecBool; DecBool→Dec)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Empty

infix 4 _≤ᵇ_

_≤ᵇ_ : ℕ → ℕ → Bool
m ≤ᵇ n = Dec→Bool (≤Dec m n)

≤ᵇ→≤ : ∀ {m n} → Bool→Type (m ≤ᵇ n) → m ≤ n
≤ᵇ→≤ {m} {n} = DecBool→Dec (≤Dec m n)

≤→≤ᵇ : ∀ {m n} → m ≤ n → Bool→Type (m ≤ᵇ n)
≤→≤ᵇ {m} {n} = Dec→DecBool (≤Dec m n)

-- The strict version, needed to split the weight trichotomy in `thinmerge`.
infix 4 _<ᵇ_

_<ᵇ_ : ℕ → ℕ → Bool
m <ᵇ n = Dec→Bool (<Dec m n)

<ᵇ→< : ∀ {m n} → Bool→Type (m <ᵇ n) → m < n
<ᵇ→< {m} {n} = DecBool→Dec (<Dec m n)

<→<ᵇ : ∀ {m n} → m < n → Bool→Type (m <ᵇ n)
<→<ᵇ {m} {n} = Dec→DecBool (<Dec m n)

<ᵇ-true→< : ∀ {m n} → (m <ᵇ n) ≡ true → m < n
<ᵇ-true→< {m} {n} eq = <ᵇ→< (subst Bool→Type (sym eq) tt)

<→<ᵇ-true : ∀ {m n} → m < n → (m <ᵇ n) ≡ true
<→<ᵇ-true {m} {n} m<n with m <ᵇ n | inspect (m <ᵇ_) n
... | true  | _        = refl
... | false | [ eq ]ᵢ  = Cubical.Data.Empty.rec (subst Bool→Type eq (<→<ᵇ m<n))

≤ᵇ-true→≤ : ∀ {m n} → (m ≤ᵇ n) ≡ true → m ≤ n
≤ᵇ-true→≤ {m} {n} eq = ≤ᵇ→≤ (subst Bool→Type (sym eq) tt)

≤→≤ᵇ-true : ∀ {m n} → m ≤ n → (m ≤ᵇ n) ≡ true
≤→≤ᵇ-true {m} {n} m≤n with m ≤ᵇ n | inspect (m ≤ᵇ_) n
... | true  | _        = refl
... | false | [ eq ]ᵢ  = Cubical.Data.Empty.rec (subst Bool→Type eq (≤→≤ᵇ m≤n))

-- Case analysis on a Boolean that remembers which way it went, so a proof can
-- follow `thinmerge`'s if_then_else_ structure without `with` (which would
-- again lose the lexicographic descent and fail termination checking).
if-split : ∀ {ℓ ℓ'} {A : Type ℓ} (P : A → Type ℓ') (b : Bool) {x y : A}
         → (b ≡ true → P x) → (b ≡ false → P y) → P (if b then x else y)
if-split P true  pt pf = pt refl
if-split P false pt pf = pf refl

-- `and` reflects a pair of Boolean facts, in both directions.
and-true : ∀ a b → (a and b) ≡ true → (a ≡ true) × (b ≡ true)
and-true true  true  _ = refl , refl
and-true true  false p = Cubical.Data.Empty.rec (false≢true p)
and-true false _     p = Cubical.Data.Empty.rec (false≢true p)

-- Reading a `false` ≤-comparison as the reverse ordering.
≤ᵇ-false→≰ : ∀ {m n} → (m ≤ᵇ n) ≡ false → ¬ (m ≤ n)
≤ᵇ-false→≰ eq m≤n = true≢false (sym (≤→≤ᵇ-true m≤n) ∙ eq)

≰→≥ : ∀ {m n} → ¬ (m ≤ n) → n ≤ m
≰→≥ {m} {n} ¬m≤n with splitℕ-≤ m n
... | _⊎_.inl m≤n = Cubical.Data.Empty.rec (¬m≤n m≤n)
... | _⊎_.inr n<m = <-weaken n<m

-- Case analysis on any Bool-valued expression, keeping the equation.
bool-split : ∀ {ℓ'} (b : Bool) (P : Type ℓ') → (b ≡ true → P) → (b ≡ false → P) → P
bool-split true  P pt pf = pt refl
bool-split false P pt pf = pf refl

-- Reading a `false` comparison as the reverse ordering.
<ᵇ-false→≮ : ∀ {m n} → (m <ᵇ n) ≡ false → ¬ (m < n)
<ᵇ-false→≮ eq m<n = true≢false (sym (<→<ᵇ-true m<n) ∙ eq)

≮→≥ : ∀ {m n} → ¬ (m < n) → n ≤ m
≮→≥ {m} {n} ¬m<n with splitℕ-< m n
... | _⊎_.inl m<n = Cubical.Data.Empty.rec (¬m<n m<n)
... | _⊎_.inr n≤m = n≤m
