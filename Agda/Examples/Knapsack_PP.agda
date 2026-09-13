{-# OPTIONS --cubical --guardedness #-}
-- The main derivation at the level of sets: knapsackImpl, an ordinary foldr
-- over a set of candidates, refines the knapsack specification.  This is the
-- special case T = ℙ of Examples.Knapsack (so `mem = collect = id`), using
-- Thin.ThinQ in place of ThinT.ThinT and Impl_PP in place of Impl.
--
-- One consequence of T = ℙ: `minR <=< thin` is not a well-formed term, since
-- `minR =<< S'` for S' : ℙ (ℙ (List Item)) would need an existential over a
-- Type₁ inside an hProp ℓ-zero.  So, as in ThinQ's universal property, every
-- composition through ℙ (ℙ _) is stated pointwise: "for every t ∈ h x, …".
--
--   Base    -- items, val/wgt, withinW, subsw
--   Order   -- _≥ₛ_ (total, for minR) and _⊴_ (partial, for thinning)
--   Spec    -- generate-and-filter = fold  (knapsack-thm, §4.1)
--   Impl_PP -- add, and thinmerge with its specification
module Examples.Knapsack_PP where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Cubical.Data.Sigma.Base using (_×_; Σ)
open import Cubical.Data.Sum.Base using (_⊎_)
open import Cubical.Data.Bool using (if_then_else_)
open import Cubical.Data.List hiding (rec; foldr; map)
open import Cubical.Data.Empty using (elim*)
open import Cubical.Data.Unit using (tt)

open import Monad_v2
open import Min
open import MonadicList
open import Sets
open import Reasoning
open import NatBool
open import HasMin
import Thin as Thinning

open import Examples.Knapsack.Base    public
open import Examples.Knapsack.Order   public
open import Examples.Knapsack.Spec    public
open import Examples.Knapsack.Impl_PP public

open HasMinProps _≥ₛ_ Max≥ₛ ≥ₛ-refl ≥ₛ-trans ≥ₛ-total


-- `thin` and `thinmerge` are abstract: take an implementation of the thinning
-- interface for _⊴_ and of the thinmerge specification as parameters, exactly
-- as `Max≥ₛ` supplies `minR` for _≥ₛ_ above.
module _ (thinD : Thinning.ThinQ _⊴_) (tmD : ThinMerge) where
  open Thinning.ThinQ thinD
  open ThinMerge tmD

  -- The step of the thinned fold: thin after one step of subsw.  Written in
  -- exactly the form thinning-thm produces, so that step is by refl.
  thinStep : Wgt → Item → ℙ (List Item) → ℙ (ℙ (List Item))
  thinStep w = λ x → thin ∘ (λ s → subsw w x =<< s)

  -- Step (27): minR <=< thin ⊑ minR, pointwise.  Thinning only ever discards
  -- a candidate that some survivor dominates, and dominance implies ⪰
  -- (⊴-⊆-≥ₛ), so a ⪰-maximum of the thinned set is still a ⪰-maximum of the
  -- original.
  minR-thin : (S t : ℙ (List Item)) → t ∈ thin S → minR t ⊆ minR S
  minR-thin S t t∈thin y y∈min-t =
    set-property-⇐ S (return y) y⊆S best y (y∈[y] y)
    where
      -- what thinning guarantees about t
      t⊆S : t ⊆ S
      t⊆S = fst (thin-universal-property-set-⇒ S t t∈thin)

      dominated : ∀ a → a ∈ S → Dom t a
      dominated = snd (thin-universal-property-set-⇒ S t t∈thin)

      -- what minR guarantees about y inside t
      props = set-property-⇒ t (return y)
                (elem_subset_singleton (minR t) y y∈min-t)

      y∈t : y ∈ t
      y∈t = fst props y (y∈[y] y)

      y-max : ∀ v → v ∈ t → y ∈ _≥ₛ_ v
      y-max v v∈t = snd props y (y∈[y] y) v v∈t

      y⊆S : return y ⊆ S
      y⊆S = elem_subset_singleton S y (t⊆S y y∈t)

      -- y beats every a ∈ S: pick a survivor v ∈ t dominating a,
      -- then y ⪰ v ⪰ a.
      best : ∀ y' → y' ∈ return y → ∀ a → a ∈ S → y' ∈ _≥ₛ_ a
      best y' y'∈ret a a∈S =
        rec squash₁
          (λ y≡y' → subst (λ u → u ∈ _≥ₛ_ a) y≡y'
            (rec squash₁
               (λ { (v , v∈t , v⊵a) →
                      ≥ₛ-trans y v a (y-max v v∈t) (⊴-⊆-≥ₛ a v v⊵a) })
               (dominated a a∈S)))
          y'∈ret

  -- minR <=< foldrM (thinStep w) (thin (return [])) ⊑ knapsack w, pointwise:
  -- any t produced by the thinned fold has minR t inside the specification.
  knapsack-main-derivation-part-1 : ∀ w xs t
    → t ∈ foldrM (thinStep w) (thin (return [])) xs
    → minR t ⊆ knapsack w xs
  knapsack-main-derivation-part-1 w xs t t∈fold = reasoning⊆ (
    ⊆begin
    minR t

    -- introducing thin⩽vw (27), with t ∈ thin (foldrM (subsw w) (return []) xs)
    -- supplied by the thinning-thm
    ⊆⟨ incl (minR-thin (foldrM (subsw w) (return []) xs) t
               (thinning-thm (subsw w) (return []) ⊴-R-trans (subsw-monotonic w)
                  xs t t∈fold)) ⟩
    minR (foldrM (subsw w) (return []) xs)

    -- knapsack-thm (sec 4.1)
    ≡⟨ sym (funExt⁻ (knapsack-thm w) xs) ⟩⊆
    knapsack w xs
    ⊆∎)

  -- One step of the algorithm is a valid thinning of one step of the
  -- specification over the set of candidates so far.
  knapsack-main-derivation-part-2 : ∀ t → ∀ w → ∀ x
      → return (thinmerge t (add w x t))
          ⊆ thinStep w x t
  knapsack-main-derivation-part-2 t w x = reasoning⊆ (
    ⊆begin
    return (thinmerge t (add w x t))

    -- the specification of thinmerge: it thins the union of its two arguments
    ⊆⟨ incl thinmerge-spec ⟩
    thin (t ∪ add w x t)

    -- =<<-∪-dist-right
    ≡⟨ cong thin (sym dist) ⟩⊆
    thin (subsw w x =<< t)

    -- definition of thinStep
    ≡⟨ refl ⟩⊆
    thinStep w x t
    ⊆∎)
    where
      -- subsw splits into "keep ys" ∪ "extend ys with x", and the latter
      -- is exactly `add w x t`
      dist : (subsw w x =<< t) ≡ (t ∪ add w x t)
      dist =
        (subsw w x =<< t)
          ≡⟨ =<<-∪-dist-right return (λ ys → filt (withinW w) (x ∷ ys)) t ⟩
        ((return =<< t) ∪ add w x t)
          ≡⟨ cong (_∪ add w x t) (ret-right-id t) ⟩
        (t ∪ add w x t)
          ∎

      -- thinmerge p q is a valid thinning of p ∪ q: (a) every survivor came
      -- from an input, (b) every input candidate is dominated by a survivor.
      -- the equation (29)
      thinmerge-spec : return (thinmerge t (add w x t))
                     ⊆ thin (t ∪ add w x t)
      thinmerge-spec =
        elem_subset_singleton (thin (t ∪ u)) (thinmerge t u)
          (thin-universal-property-set-⇐ (t ∪ u) (thinmerge t u)
            (thinmerge-⊆ t u , thinmerge-dom t u))
        where u = add w x t

  thin-refl : ∀ S → S ∈ thin S
  thin-refl S = thin-universal-property-set-⇐ S S
    (P.⊆-refl S , λ a a∈S → ∣ a , a∈S , ⊴-refl a ∣₁)

  -- The set of candidates kept by the algorithm is one of the sets the thinned
  -- fold may produce.
  knapsack-main-derivation-part-3 : ∀ w
    → (return ∘ foldr (λ x t → thinmerge t (add w x t)) (return []))
      ⊑ foldrM (thinStep w) (thin (return []))
  knapsack-main-derivation-part-3 w = reasoning⊑ (
    ⊑begin
    return ∘ foldr (λ x t → thinmerge t (add w x t)) (return [])

    -- a pure foldr is the foldrM whose step just returns
    ≡⟨ foldrM-pure (λ x t → thinmerge t (add w x t)) (return []) ⟩⊑
    foldrM (λ x → return ∘ (λ t → thinmerge t (add w x t))) (return (return []))

    -- part-2 on the step, thin-refl on the base
    ⊑⟨ incl⊑ (foldrM-monotonic
         (λ x → return ∘ (λ t → thinmerge t (add w x t)))
         (thinStep w)
         (return (return [])) (thin (return []))
         (λ x t → knapsack-main-derivation-part-2 t w x)
         base) ⟩
    foldrM (thinStep w) (thin (return []))
    ⊑∎)
    where
      -- the initial set of candidates, return [], is kept by thinning
      base : return (return []) ⊆ thin (return [])
      base = elem_subset_singleton (thin (return [])) (return []) (thin-refl (return []))

  -- minR of the algorithm's candidates refines the specification: part-1 at
  -- the set that part-3 says the algorithm produces.
  knapsack-main-derivation-final : ∀ w xs
    → knapsackImpl w xs ⊆ knapsack w xs
  knapsack-main-derivation-final w xs =
    knapsack-main-derivation-part-1 w xs
      (foldr (λ x t → thinmerge t (add w x t)) (return []) xs)
      (knapsack-main-derivation-part-3 w xs _ (y∈[y] _))

  -- The final result
  knapsack-main-derivation-final-eq : ∀ w
      → knapsackImpl w ⊑ knapsack w
  knapsack-main-derivation-final-eq w = knapsack-main-derivation-final w

  -- however, if the algorithm is not total: it may return ∅, and 
  -- ∀ w ­→ const ∅ ⊑ knapsack w is always a valid refinement.
  dummy-algorithm : ∀ w → const ∅ ⊑ knapsack w
  dummy-algorithm w = λ _ _ ()

  -- [ Totality of knapsackImpl]

  -- A thinning of S has a ⪰-maximum whenever S does: thinning keeps a
  -- survivor v dominating S's maximum y, and v ⪰ y ⪰ everything in t ⊆ S.
  thin-minR-total : (S t : ℙ (List Item)) → t ∈ thin S
    → ∥ Σ (List Item) (λ y → y ∈ minR S) ∥₁
    → ∥ Σ (List Item) (λ v → v ∈ minR t) ∥₁
  thin-minR-total S t t∈thin = rec squash₁ lift-max
    where
      t⊆S : t ⊆ S
      t⊆S = fst (thin-universal-property-set-⇒ S t t∈thin)

      dominated : ∀ a → a ∈ S → Dom t a
      dominated = snd (thin-universal-property-set-⇒ S t t∈thin)

      lift-max : Σ (List Item) (λ y → y ∈ minR S) → ∥ Σ (List Item) (λ v → v ∈ minR t) ∥₁
      lift-max (y , y∈min) =
        rec squash₁
          (λ { (v , v∈t , v⊵y) →
                 ∣ v , minR-property-⇐ t v v∈t
                         (λ z z∈t → ≥ₛ-trans v y z (⊴-⊆-≥ₛ y v v⊵y) (y-max z (t⊆S z z∈t))) ∣₁ })
          (dominated y y∈S)
        where
          y∈S   = fst (minR-property-⇒ S y y∈min)
          y-max = snd (minR-property-⇒ S y y∈min)

  -- The algorithm always produces an answer.  Together with
  -- knapsack-main-derivation-final-eq: it returns some optimal selection, and
  -- nothing but optimal selections.
  
  knapsack-total : ∀ w xs → ∥ Σ (List Item) (λ y → y ∈ knapsackImpl w xs) ∥₁
  knapsack-total w xs = thin-minR-total C F F∈thinC spec-max
    where
      C = foldrM (subsw w) (return []) xs
      F = foldr (λ x t → thinmerge t (add w x t)) (return []) xs

      -- part-3 puts F in the thinned fold; thinning-thm puts that in thin C
      F∈thinC : F ∈ thin C
      F∈thinC = thinning-thm (subsw w) (return []) ⊴-R-trans (subsw-monotonic w) xs F
                  (knapsack-main-derivation-part-3 w xs F (y∈[y] F))

      spec-max : ∥ Σ (List Item) (λ y → y ∈ minR C) ∥₁
      spec-max = hasmin-foldrM-finite 
        (subsw w) 
        (return [])
        (finite-return [])
        (λ x ys → 
          finite-∪ (return ys) (filt (withinW w) (x ∷ ys))
          (finite-return ys) (finite-filt (withinW w) (x ∷ ys)))
        (∣ [] , y∈[y] [] ∣₁)
        (λ x ys → ∣ ys , ∣ _⊎_.inl (y∈[y] ys) ∣₁ ∣₁)
        (xs)