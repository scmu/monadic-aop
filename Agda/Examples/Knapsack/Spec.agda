{-# OPTIONS --cubical --guardedness #-}
-- The specification side (§4.1): generate-and-filter equals a fold, so
-- knapsack w ≡ minR ∘ foldrM (subsw w) (return []).
module Examples.Knapsack.Spec where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path using (inspect; [_]ᵢ)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Cubical.Data.Sigma.Base using (_×_; Σ)
open import Cubical.Data.Sum.Base using (_⊎_)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.List hiding (rec; foldr; map)
open import Cubical.Data.Empty using (elim*; ⊥; rec*)

open import Monad_v2
open import Min
open import MonadicList
open import Sets
open import Reasoning
open import NatBool
open import Examples.Knapsack.Base
open import Examples.Knapsack.Order

knapsack : Wgt → List Item → ℙ (List Item)
knapsack w = minR ∘ (filt (withinW w) <=< subseq)

step : ∀ w x y → (subsw w x =<< filt (withinW w) y) ⊆ (filt (withinW w) =<< subs x y)
step w x y z z∈lhs with withinW w y | inspect (withinW w) y
... | false | _ = rec* (subst (λ S → z ∈ S) (=<<-∅ (subsw w x)) z∈lhs)
... | true | [ eq ]ᵢ = rec (P.∈-isProp (filt (withinW w) =<< subs x y) z) helper
                 (subst (λ S → z ∈ S) (ret-left-id y (subsw w x)) z∈lhs)
  where
    fty : filt (withinW w) y ≡ return y
    fty = filt-true (withinW w) y eq

    helper : (z ∈ return y) ⊎ (z ∈ filt (withinW w) (x ∷ y)) → z ∈ (filt (withinW w) =<< subs x y)
    helper (_⊎_.inl y≡z) = ∣ y , ∣ _⊎_.inl ∣ refl ∣₁ ∣₁ , subst (λ S → z ∈ S) (sym fty) y≡z ∣₁
    helper (_⊎_.inr z∈fxy) = ∣ x ∷ y , ∣ _⊎_.inr ∣ refl ∣₁ ∣₁ , z∈fxy ∣₁

fusion-cond : ∀ w x m → (subsw w x =<< (filt (withinW w) =<< m)) ⊆ (filt (withinW w) =<< (subs x =<< m))
fusion-cond w x m = reasoning⊆ (
  ⊆begin
  subsw w x =<< (filt (withinW w) =<< m)
  
  ≡⟨ >>=-assoc m (filt (withinW w)) (subsw w x) ⟩⊆
  (λ y → subsw w x =<< filt (withinW w) y) =<< m
  
  ⊆⟨ incl (=<<-monotonic-left m (λ y → subsw w x =<< filt (withinW w) y) (λ y → filt (withinW w) =<< subs x y) (step w x)) ⟩
  (λ y → filt (withinW w) =<< subs x y) =<< m
  
  ≡⟨ sym (>>=-assoc m (subs x) (filt (withinW w))) ⟩⊆
  filt (withinW w) =<< (subs x =<< m)
  ⊆∎)

h-e-eq : (w : Wgt) → filt (withinW w) =<< return [] ≡ return []
h-e-eq w = ret-left-id [] (filt (withinW w))

knapsack-fusion : ∀ w → foldrM (subsw w) (filt (withinW w) =<< return [])
                        ⊑ (λ n → filt (withinW w) =<< n) ∘ foldrM subs (return [])
knapsack-fusion w = foldrM-fusion (subsw w) subs (return []) (λ n → filt (withinW w) =<< n) (fusion-cond w)

knapsack-sound : ∀ w → foldrM (subsw w) (return []) ⊑ (filt (withinW w) <=< subseq)
knapsack-sound w = reasoning⊑ (
  ⊑begin
  foldrM (subsw w) (return [])
  
  ≡⟨ cong (foldrM (subsw w)) (sym (h-e-eq w)) ⟩⊑
  foldrM (subsw w) (filt (withinW w) =<< return [])
  
  ⊑⟨ incl⊑ (knapsack-fusion w) ⟩
  (λ n → filt (withinW w) =<< n) ∘ foldrM subs (return [])
  
  ≡⟨ cong (λ f → (λ n → filt (withinW w) =<< n) ∘ f) (sym (subseq-is-foldrM {X = Item})) ⟩⊑
  filt (withinW w) <=< subseq
  ⊑∎)

-- Full equality: foldrM (subsw w) (return []) ≡ filt (withinW w) <=< subseq.
-- Weight only grows as items are added, so eagerly discarding an over-capacity
-- extension (subsw) never throws away anything that generate-then-filter would keep.

swap-lemma : ∀ w x S → ((λ y → filt (withinW w) (x ∷ y)) =<< S) ≡ ((λ y → filt (withinW w) (x ∷ y)) =<< (filt (withinW w) =<< S))
swap-lemma w x S = P.⊆-antisym _ _ lhs⊆rhs rhs⊆lhs
  where
    lhs⊆rhs : ((λ y → filt (withinW w) (x ∷ y)) =<< S) ⊆ ((λ y → filt (withinW w) (x ∷ y)) =<< (filt (withinW w) =<< S))
    lhs⊆rhs z z∈ = rec (P.∈-isProp ((λ y → filt (withinW w) (x ∷ y)) =<< (filt (withinW w) =<< S)) z) helper z∈
      where
        helper : Σ _ (λ y → (y ∈ S) × (z ∈ filt (withinW w) (x ∷ y))) → z ∈ ((λ y → filt (withinW w) (x ∷ y)) =<< (filt (withinW w) =<< S))
        helper (y , y∈S , z∈fxy) with withinW w (x ∷ y) | inspect (withinW w) (x ∷ y)
        ... | false | [ eq ]ᵢ = rec* z∈fxy
        ... | true  | [ eq ]ᵢ = ∣ y , y∈filtWy , subst (λ F → z ∈ F) (sym (filt-true (withinW w) (x ∷ y) eq)) z∈fxy ∣₁
          where
            y-valid : withinW w y ≡ true
            y-valid = within-mono-⇒ w x y eq

            y∈filtWy : y ∈ (filt (withinW w) =<< S)
            y∈filtWy = ∣ y , y∈S , subst (λ F → y ∈ F) (sym (filt-true (withinW w) y y-valid)) ∣ refl ∣₁ ∣₁

    rhs⊆lhs : ((λ y → filt (withinW w) (x ∷ y)) =<< (filt (withinW w) =<< S)) ⊆ ((λ y → filt (withinW w) (x ∷ y)) =<< S)
    rhs⊆lhs = =<<-monotonic-right (λ y → filt (withinW w) (x ∷ y)) (filt (withinW w) =<< S) S (filt-⊆ (withinW w) S)

knapsack-main-step : ∀ w x xs → (filt (withinW w) <=< subseq) (x ∷ xs) ≡ subsw w x =<< (filt (withinW w) <=< subseq) xs
knapsack-main-step w x xs =
  filt (withinW w) =<< (subseq xs ∪ (_∷_ x) <$> subseq xs)
  ≡⟨ =<<-∪-dist-left (filt (withinW w)) (subseq xs) ((_∷_ x) <$> subseq xs) ⟩
  
  (filt (withinW w) =<< subseq xs) ∪ (filt (withinW w) =<< ((_∷_ x) <$> subseq xs))
  ≡⟨ cong (λ S → h xs ∪ S) (=<<-<$>-fusion (filt (withinW w)) (_∷_ x) (subseq xs)) ⟩
  
  h xs ∪ ((λ y → filt (withinW w) (x ∷ y)) =<< subseq xs)
  
  ≡⟨ cong (λ S → h xs ∪ S) (swap-lemma w x (subseq xs)) ⟩
  h xs ∪ ((λ y → filt (withinW w) (x ∷ y)) =<< h xs)
  
  ≡⟨ cong (λ S → S ∪ ((λ y → filt (withinW w) (x ∷ y)) =<< h xs)) (sym (ret-right-id (h xs))) ⟩
  (h xs >>= return) ∪ ((λ y → filt (withinW w) (x ∷ y)) =<< h xs)
  
  ≡⟨ sym (=<<-∪-dist-right return (λ y → filt (withinW w) (x ∷ y)) (h xs)) ⟩
  subsw w x =<< h xs
  ∎
  where h = filt (withinW w) <=< subseq

knapsack-eq : ∀ w → (filt (withinW w) <=< subseq {X = Item}) ≡ foldrM (subsw w) (return [])
knapsack-eq w = foldrM-fixed-point-properties-eq⇐ {A = Item} {B = List Item} (subsw w) (return []) (filt (withinW w) <=< subseq)
                  (h-e-eq w , knapsack-main-step w)

knapsack-thm : ∀ w → knapsack w ≡ minR ∘ foldrM (subsw w) (return [])
knapsack-thm w = cong (minR ∘_) (knapsack-eq w)
