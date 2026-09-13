{-# OPTIONS --cubical --guardedness #-}
-- The algorithm at the level of sets: the special case T = ℙ of
-- Examples.Knapsack.Impl, where `mem = collect = id`.
--
-- On sets there is nothing to compute, so `thinmerge` cannot be written by
-- recursion as it is on lists.  Instead it is an abstract operation on sets
-- that comes with its specification (the equation (29) of the paper): every
-- survivor is one of the inputs, and every input is dominated by a survivor.
-- Likewise there is no `head` of a set: the algorithm returns `minR` of the
-- set of surviving candidates.  None of this mentions the abstract `thin`.
module Examples.Knapsack.Impl_PP where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Cubical.Data.Sigma.Base using (_×_; Σ)
open import Cubical.Data.List hiding (rec; foldr; map)

open import Monad_v2
open import Min
open import MonadicList
open import Sets
open import Examples.Knapsack.Base
open import Examples.Knapsack.Order

-- "some survivor x of xs dominates y"
Dom : ℙ (List Item) → List Item → Type ℓ-zero
Dom xs y = ∥ Σ (List Item) (λ x → (x ∈ xs) × (x ∈ _⊴_ y)) ∥₁

add : Wgt → Item → ℙ (List Item) → ℙ (List Item)
add w x t = (filt (withinW w) ∘ (_∷_ x)) =<< t

-- The specification of thinmerge: it thins the union of its two arguments.
record ThinMerge : Type (ℓ-suc ℓ-zero) where
  field
    thinmerge : ℙ (List Item) → ℙ (List Item) → ℙ (List Item)

    -- (a) every survivor of thinmerge came from one of its two inputs.
    thinmerge-⊆ : ∀ p q → thinmerge p q ⊆ (p ∪ q)

    -- (b) every candidate in either input is dominated by some survivor.
    thinmerge-dom : ∀ p q y → y ∈ (p ∪ q) → Dom (thinmerge p q) y

  -- The fold keeps a set of surviving candidates; the answer is its best.
  knapsackImpl : Wgt → List Item → ℙ (List Item)
  knapsackImpl w = minR ∘ foldr (λ x t → thinmerge t (add w x t)) (return [])
