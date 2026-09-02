{-# OPTIONS --cubical --guardedness #-}
-- The main derivation: knapsackImpl, an ordinary foldr over lists, refines
-- the knapsack specification.  This is the only part that depends on the
-- abstract `thin`; the algorithm itself lives in Examples.Knapsack.Impl.
--
--   Base  -- items, val/wgt, withinW, subsw
--   Order -- _≥ₛ_ (total, for minR) and _⊴_ (partial, for thinning)
--   Spec  -- generate-and-filter = fold  (knapsack-thm, §4.1)
--   Impl  -- thinmerge / add and their invariants
module Examples.Knapsack where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Cubical.Data.Sigma.Base using (_×_; Σ)
open import Cubical.Data.Sum.Base using (_⊎_)
open import Cubical.Data.List hiding (rec; foldr; map)
open import Cubical.Data.Empty using (elim*; ⊥)

open import Monad_v2
open import Min
open import MonadicList
open import Sets
open import Reasoning
open import NatBool
import ThinT as Thinning
open Thinning using (T; mem; collect; collect-ret; collect-∪; collect-mem; mem-mergeT; mergeT)

open import Examples.Knapsack.Base   public
open import Examples.Knapsack.Order  public
open import Examples.Knapsack.Spec   public
open import Examples.Knapsack.Impl   public

-- `thin` is abstract: take an implementation of the thinning interface for _⊴_
-- as a parameter, exactly as `Max≥ₛ` supplies `minR` for _≥ₛ_ above.
module _ (thinD : Thinning.ThinT _⊴_) where
  open Thinning.ThinT thinD

  -- Step (27): (minR ∘ mem) <=< thin ⊑ minR.  Thinning only ever discards a
  -- candidate that some survivor dominates, and dominance implies ⪰ (⊴-⊆-≥ₛ),
  -- so a ⪰-maximum of the thinned set is still a ⪰-maximum of the original.
  minR-thin : {Y : Type ℓ-zero} (g : Y → ℙ (List Item))
            → (minR ∘ mem) <=< (thin ∘ collect ∘ g) ⊑ minR ∘ g
  minR-thin g x y y∈ = rec (P.∈-isProp (minR (g x)) y) helper y∈
    where
      helper : Σ (T (List Item)) (λ t → (t ∈ thin (collect (g x))) × (y ∈ minR (mem t)))
             → y ∈ minR (g x)
      helper (t , t∈thin , y∈min-mem-t) =
        set-property-⇐ (g x) (return y) y⊆gx best y (y∈[y] y)
        where
          -- what thinning guarantees about t, stated directly about the set g x
          mem-t⊆gx : mem t ⊆ g x
          mem-t⊆gx = fst (thin-collect-⇒ (g x) t t∈thin)

          dominated : ∀ a → a ∈ g x → ∥ Σ (List Item) (λ v → (v ∈ mem t) × (v ∈ _⊴_ a)) ∥₁
          dominated = snd (thin-collect-⇒ (g x) t t∈thin)

          -- what minR guarantees about y inside mem t
          props = set-property-⇒ (mem t) (return y)
                    (elem_subset_singleton (minR (mem t)) y y∈min-mem-t)

          y∈mem-t : y ∈ mem t
          y∈mem-t = fst props y (y∈[y] y)

          y-max : ∀ v → v ∈ mem t → y ∈ _≥ₛ_ v
          y-max v v∈mem-t = snd props y (y∈[y] y) v v∈mem-t

          y⊆gx : return y ⊆ g x
          y⊆gx = elem_subset_singleton (g x) y (mem-t⊆gx y y∈mem-t)

          -- y beats every a ∈ g x: pick a survivor v ∈ mem t dominating a,
          -- then y ⪰ v ⪰ a.
          best : ∀ y' → y' ∈ return y → ∀ a → a ∈ g x → y' ∈ _≥ₛ_ a
          best y' y'∈ret a a∈gx =
            rec squash₁
              (λ y≡y' → subst (λ u → u ∈ _≥ₛ_ a) y≡y'
                (rec squash₁
                   (λ { (v , v∈mem-t , v⊵a) →
                          ≥ₛ-trans y v a (y-max v v∈mem-t) (⊴-⊆-≥ₛ a v v⊵a) })
                   (dominated a a∈gx)))
              y'∈ret

  knapsack-main-derivation-part-1 : ∀ w
    → (minR ∘ mem) <=< foldrM (λ x → thin ∘ collect ∘ subsw w x <=< mem) ((thin ∘ collect) (return []))
    ⊑ knapsack w
  knapsack-main-derivation-part-1 w = reasoning⊑ (
    ⊑begin
    (minR ∘ mem) <=< foldrM (λ x → thin ∘ collect ∘ subsw w x <=< mem) ((thin ∘ collect) (return []))

    -- thinning-thm, under ((minR ∘ mem) <=<_)
    ⊑⟨ incl⊑ (<=<-monotonic-right (minR ∘ mem)
         (foldrM (λ x → thin ∘ collect ∘ subsw w x <=< mem) ((thin ∘ collect) (return [])))
         (thin ∘ collect ∘ foldrM (subsw w) (return []))
         (thinning-thm (subsw w) (return []) ⊴-R-trans (subsw-monotonic w))) ⟩
    (minR ∘ mem) <=< (thin ∘ collect ∘ foldrM (subsw w) (return []))

    
    -- introducing thin⩽vw (27)
    ⊑⟨ incl⊑ (minR-thin (foldrM (subsw w) (return []))) ⟩
    minR ∘ foldrM (subsw w) (return [])

    -- knapsack-thm (sec 4.1)
    ≡⟨ sym (knapsack-thm w) ⟩⊑
    knapsack w
    ⊑∎)

  knapsack-main-derivation-part-2 : ∀ t → ∀ w → ∀ x → return (thinmerge t (add w x t)) ⊆ (thin ∘ collect ∘ subsw w x <=< mem) t
  knapsack-main-derivation-part-2 t w x = reasoning⊆ (
    ⊆begin
    return (thinmerge t (add w x t))

    -- the specification of thinmerge: it thins the merge of its two arguments
    ⊆⟨ incl thinmerge-spec ⟩
    thin (mergeT t (add w x t))
    
    -- collect (mem t) ≡ t
    ≡⟨ cong (λ z → thin (mergeT z (add w x t))) (sym (collect-mem t)) ⟩⊆
    thin (mergeT (collect (mem t)) (add w x t))

    -- collect-∪ / =<<-∪-dist-right
    ≡⟨ cong thin (sym collect-dist) ⟩⊆
    thin (collect (subsw w x =<< mem t))

    -- definition of _<=<_ and _∘_
    ≡⟨ refl ⟩⊆
    (thin ∘ collect ∘ subsw w x <=< mem) t
    ⊆∎)
    where
      -- the candidates reachable by actually taking x, i.e. what `add` collects
      addSet : ℙ (List Item)
      addSet = (filt (withinW w) ∘ (_∷_ x)) =<< mem t

      -- subsw splits into "keep ys" ∪ "extend ys with x"
      dist : (subsw w x =<< mem t) ≡ (mem t ∪ addSet)
      dist =
        (subsw w x =<< mem t)
          ≡⟨ =<<-∪-dist-right return (λ ys → filt (withinW w) (x ∷ ys)) (mem t) ⟩
        ((return =<< mem t) ∪ addSet)
          ≡⟨ cong (_∪ addSet) (ret-right-id (mem t)) ⟩
        (mem t ∪ addSet)
          ∎

      -- collect turns that ∪ into a mergeT, and collect addSet *is* add w x t
      collect-dist : collect (subsw w x =<< mem t) ≡ mergeT (collect (mem t)) (add w x t)
      collect-dist = cong collect dist ∙ collect-∪ (mem t) addSet

      -- thinmerge p q is a valid thinning of the merge of p and q: (a) every
      -- survivor came from an input, (b) every input candidate is dominated by
      -- a survivor. mem-mergeT bridges mem (mergeT p q) and mem p ∪ mem q.
      -- the equation (29)
      thinmerge-spec : return (thinmerge t (add w x t))
                     ⊆ thin (mergeT t (add w x t))
      thinmerge-spec =
        elem_subset_singleton (thin (mergeT t u)) (thinmerge t u)
          (thin-universal-property-set-⇐ (mergeT t u) (thinmerge t u)
            ( (λ a a∈ → subst (λ S → a ∈ S) (sym (mem-mergeT t u)) (thinmerge-⊆ t u a a∈))
            , (λ a a∈ → thinmerge-dom t u a (subst (λ S → a ∈ S) (mem-mergeT t u) a∈)) ))
        where u = add w x t

  thin-refl : ∀ t → t ∈ thin t
  thin-refl t = thin-universal-property-set-⇐ t t
    (P.⊆-refl (mem t) , λ a a∈mem-t → ∣ a , a∈mem-t , ⊴-refl a ∣₁)

  knapsack-main-derivation-part-3 : ∀ w
    → return ∘ head ∘ foldr (λ x t → thinmerge t (add w x t)) [ [] ]
      ⊑ (minR ∘ mem) <=< foldrM (λ x → thin ∘ collect ∘ subsw w x <=< mem) ((thin ∘ collect) (return []))
  knapsack-main-derivation-part-3 w = reasoning⊑ (
    ⊑begin
    return ∘ head ∘ foldr (λ x t → thinmerge t (add w x t)) [ [] ]

    -- T is a sorted list
    ⊑⟨ incl⊑ (head-is-max w) ⟩
    (minR ∘ mem) ∘ foldr (λ x t → thinmerge t (add w x t)) [ [] ]

    -- f ∘ g = f <=< (return ∘ g)
    ≡⟨ sym (<=<-right-id-pure (minR ∘ mem) (foldr (λ x t → thinmerge t (add w x t)) [ [] ])) ⟩⊑
    (minR ∘ mem) <=< (return ∘ foldr (λ x t → thinmerge t (add w x t)) [ [] ])

    -- part-2, under ((minR ∘ mem) <=<_)
    ⊑⟨ incl⊑ (<=<-monotonic-right (minR ∘ mem)
         (return ∘ foldr (λ x t → thinmerge t (add w x t)) [ [] ])
         (foldrM (λ x → thin ∘ collect ∘ subsw w x <=< mem) ((thin ∘ collect) (return [])))
         pure-fold⊑foldrM) ⟩
    (minR ∘ mem) <=< foldrM (λ x → thin ∘ collect ∘ subsw w x <=< mem) ((thin ∘ collect) (return []))
    ⊑∎)
    where
      -- collect (return []) is singleT [] = [ [] ], which thinning keeps.
      base : return [ [] ] ⊆ (thin ∘ collect) (return [])
      base = elem_subset_singleton ((thin ∘ collect) (return [])) [ [] ]
               (subst (λ u → [ [] ] ∈ thin u) (sym (collect-ret [])) (thin-refl [ [] ]))

      pure-fold⊑foldrM :
        (return ∘ foldr (λ x t → thinmerge t (add w x t)) [ [] ])
        ⊑ foldrM (λ x → thin ∘ collect ∘ subsw w x <=< mem) ((thin ∘ collect) (return []))
      pure-fold⊑foldrM = reasoning⊑ (
        ⊑begin
        return ∘ foldr (λ x t → thinmerge t (add w x t)) [ [] ]

        -- a pure foldr is the foldrM whose step just returns
        ≡⟨ foldrM-pure (λ x t → thinmerge t (add w x t)) [ [] ] ⟩⊑
        foldrM (λ x → return ∘ (λ t → thinmerge t (add w x t))) (return [ [] ])

        -- part-2 on the step, thin-refl on the base
        ⊑⟨ incl⊑ (foldrM-monotonic
             (λ x → return ∘ (λ t → thinmerge t (add w x t)))
             (λ x → thin ∘ collect ∘ subsw w x <=< mem)
             (return [ [] ]) ((thin ∘ collect) (return []))
             (λ x t → knapsack-main-derivation-part-2 t w x)
             base) ⟩
        foldrM (λ x → thin ∘ collect ∘ subsw w x <=< mem) ((thin ∘ collect) (return []))
        ⊑∎)

  knapsack-main-derivation-final : ∀ w 
    → return ∘ head ∘ foldr (λ x t → thinmerge t (add w x t)) [ [] ] ⊑ knapsack w
  knapsack-main-derivation-final w =
    ⊑-trans {r = return ∘ head ∘ foldr (λ x t → thinmerge t (add w x t)) [ [] ]}
            {s = (minR ∘ mem) <=< foldrM (λ x → thin ∘ collect ∘ subsw w x <=< mem) ((thin ∘ collect) (return []))}
            {t = knapsack w}
            (knapsack-main-derivation-part-3 w) (knapsack-main-derivation-part-1 w)

  
  -- The final result
  knapsack-main-derivation-final-eq : ∀ w → return ∘ (knapsackImpl w) ⊑ knapsack w
  knapsack-main-derivation-final-eq w = knapsack-main-derivation-final w
