{-# OPTIONS --cubical --guardedness #-}
-- Basic knapsack vocabulary: items, their value and weight, the capacity
-- test, and the one-step candidate generator.
module Examples.Knapsack.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path using (inspect; [_]ᵢ)
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Cubical.Data.Sigma.Base using (_×_)
open import Cubical.Data.Nat using (ℕ; _+_)
open import Cubical.Data.Nat.Order as Order using (_≤_; ≤-trans)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Bool.Properties using (true≢false; false≢true)
open import Cubical.Data.List hiding (rec; foldr; map)
open import Cubical.Data.List as List using () renaming (map to mapList)
import Cubical.Data.Empty

open import Monad_v2
open import MonadicList
open import Sets
open import NatBool

Val : Type ℓ-zero
Val = ℕ

Wgt : Type ℓ-zero
Wgt = ℕ

Item : Type ℓ-zero
Item = Val × Wgt

sumℕ : List ℕ → ℕ
sumℕ [] = 0
sumℕ (x ∷ xs) = x + sumℕ xs

val : List Item → Val
val items = sumℕ (mapList fst items)

wgt : List Item → Wgt
wgt items = sumℕ (mapList snd items)

withinW : Wgt → List Item → Bool
withinW w xs = wgt xs ≤ᵇ w

subsw : Wgt → Item → List Item → ℙ (List Item)
subsw w x ys = return ys ∪ filt (withinW w) (x ∷ ys)

wgt-∷-≥ : ∀ x y → wgt y ≤ wgt (x ∷ y)
wgt-∷-≥ x y = snd x , refl

within-mono-⇒ : ∀ w x y → withinW w (x ∷ y) ≡ true → withinW w y ≡ true
within-mono-⇒ w x y eq = ≤→≤ᵇ-true (Order.≤-trans (wgt-∷-≥ x y) (≤ᵇ-true→≤ eq))

within-mono-⇐ : ∀ w x y → withinW w y ≡ false → withinW w (x ∷ y) ≡ false
within-mono-⇐ w x y eq with withinW w (x ∷ y) | inspect (withinW w) (x ∷ y)
... | false | _         = refl
... | true  | [ eq2 ]ᵢ  = Cubical.Data.Empty.rec (true≢false (sym (within-mono-⇒ w x y eq2) ∙ eq))
