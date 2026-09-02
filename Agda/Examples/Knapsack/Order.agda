{-# OPTIONS --cubical --guardedness #-}
-- The two orders on candidate lists: the total value order _≥ₛ_ that `minR`
-- maximises over, and the partial dominance order _⊴_ that thinning uses.
module Examples.Knapsack.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path using (inspect; [_]ᵢ)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Cubical.Data.Sigma.Base using (_×_; Σ)
open import Cubical.Data.Sum.Base using (_⊎_)
open import Cubical.Data.Nat using (ℕ; _+_; snotz)
open import Cubical.Data.Nat.Order as Order using (_≤_; _<_; ≤-refl; ≤-trans; ≤-k+; ≤0→≡0)
open import Cubical.Data.Bool using (Bool; true; false; _and_)
open import Cubical.Data.Bool.Properties using (isSetBool)
open import Cubical.Data.List hiding (rec; foldr; map)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty using (isProp⊥; elim*; ⊥; rec*)

open import Monad_v2
open import Min
open import MonadicList
open import Sets
open import NatBool
open import Examples.Knapsack.Base

_≥ₛ_ : List Item → ℙ (List Item)
_≥ₛ_ xs = λ ys → ∥ val xs ≤ val ys ∥₁ , squash₁

Max≥ₛ : MinR _≥ₛ_
Max≥ₛ = record
  { minR = λ xs maxxs → 
      ((maxxs ∈ xs) × (∀ x → x ∈ xs → fst (_≥ₛ_ x maxxs))) , 
      isProp× (snd (xs maxxs)) (isPropΠ λ x → isPropΠ λ _ → squash₁)

  ; universal-property-⇒ = λ P f P⊑maxR∘f → 
      ( (λ x y y∈Px → fst (P⊑maxR∘f x y y∈Px))
      , (λ y y' y'∈P<=<f°y → 
          rec squash₁ 
              (λ { (x , y∈fx , y'∈Px) → snd (P⊑maxR∘f x y' y'∈Px) y y∈fx }) 
              y'∈P<=<f°y)
      )

  ; universal-property-⇐ = λ P f P⊑-h x y y∈Px → 
      let 
        (P⊑f , P<=<f°⊑R) = P⊑-h
        y∈fx = P⊑f x y y∈Px
        is-max = λ y' y'∈fx → P<=<f°⊑R y' y ∣ x , y'∈fx , y∈Px ∣₁
      in y∈fx , is-max
  }

open MinR Max≥ₛ public

≥ₛ-refl : (x : List Item) → x ∈ _≥ₛ_ x
≥ₛ-refl x = ∣ 0 , refl ∣₁

≥ₛ-trans : ∀ x y z → x ∈ _≥ₛ_ y → y ∈ _≥ₛ_ z → x ∈ _≥ₛ_ z
≥ₛ-trans x y z x≥y y≥z = PT.map2 (λ x≥y' y≥z' → Order.≤-trans y≥z' x≥y') x≥y y≥z

≥ₛ-total : ∀ x y → ∥ (x ∈ _≥ₛ_ y) ⊎ (y ∈ _≥ₛ_ x) ∥₁
≥ₛ-total x y with (val x) Order.≟ (val y)
... | Order.lt x<y = ∣ _⊎_.inr ∣ Order.<-weaken x<y ∣₁ ∣₁
... | Order.eq x≡y = ∣ _⊎_.inr ∣ 0 , x≡y ∣₁ ∣₁
... | Order.gt y<x = ∣ _⊎_.inl ∣ Order.<-weaken y<x ∣₁ ∣₁

-- [ Thinning ]

-- The thinning order. Following ThinT's convention that `y ∈ Q x` reads as
-- `y ⪰ x`, `ys ∈ (xs ⊴)` says ys dominates xs: at least as valuable, and no
-- heavier -- so ys can be extended wherever xs can. The weight component is
-- what makes `subsw w` monotonic on this order.
_⊴_ : List Item → ℙ (List Item)
_⊴_ xs ys = ∥ (val xs ≤ val ys) × (wgt ys ≤ wgt xs) ∥₁ , squash₁

⊴-refl : (x : List Item) → x ∈ _⊴_ x
⊴-refl x = ∣ (≤-refl , ≤-refl) ∣₁

-- `x ∈ _⊴_ y` unfolds to (val y ≤ val x) × (wgt x ≤ wgt y), so the two
-- components chain in opposite directions.
⊴-trans : ∀ x y z → x ∈ _⊴_ y → y ∈ _⊴_ z → x ∈ _⊴_ z
⊴-trans x y z x⊵y y⊵z =
  PT.map2 (λ { (valy≤valx , wgtx≤wgty) (valz≤valy , wgty≤wgtz) →
                 ≤-trans valz≤valy valy≤valx , ≤-trans wgtx≤wgty wgty≤wgtz })
          x⊵y y⊵z

-- Monad_v2's R-trans takes its arguments in the opposite order.
⊴-R-trans : R-trans _⊴_
⊴-R-trans x y z y∈⊴x z∈⊴y = ⊴-trans z y x z∈⊴y y∈⊴x

-- Dominance is a *partial* order, so there is no `⊴-total` to prove: [] and
-- [(5 , 5)] are incomparable -- the second is more valuable but also heavier,
-- so neither dominates the other. (Thinning does not need totality; that is
-- what separates it from greedy. The totality `minR` needs is on the
-- value-only order _≥ₛ_, already proved as `≥ₛ-total` above.)
⊴-not-total : ¬ (∀ x y → ∥ (x ∈ _⊴_ y) ⊎ (y ∈ _⊴_ x) ∥₁)
⊴-not-total total = PT.rec isProp⊥ contra (total [] ((5 , 5) ∷ []))
  where
    5≰0 : ¬ (5 ≤ 0)
    5≰0 5≤0 = snotz (≤0→≡0 5≤0)

    contra : ([] ∈ _⊴_ ((5 , 5) ∷ [])) ⊎ (((5 , 5) ∷ []) ∈ _⊴_ []) → ⊥
    contra (_⊎_.inl p) = PT.rec isProp⊥ (λ q → 5≰0 (fst q)) p
    contra (_⊎_.inr p) = PT.rec isProp⊥ (λ q → 5≰0 (snd q)) p

-- [ Deciding dominance ]

-- Dominance is a conjunction of two ℕ comparisons pointing in *opposite*
-- directions, so it needs both halves tested separately and `and`ed together.
-- `xs ⊴ᵇ ys` decides `ys ∈ _⊴_ xs`, i.e. "ys dominates xs".
infix 4 _⊴ᵇ_

_⊴ᵇ_ : List Item → List Item → Bool
xs ⊴ᵇ ys = (val xs ≤ᵇ val ys) and (wgt ys ≤ᵇ wgt xs)

⊴ᵇ→⊴ : ∀ xs ys → (xs ⊴ᵇ ys) ≡ true → ys ∈ _⊴_ xs
⊴ᵇ→⊴ xs ys p =
  ∣ ≤ᵇ-true→≤ (fst (and-true _ _ p)) , ≤ᵇ-true→≤ (snd (and-true _ _ p)) ∣₁

⊴→⊴ᵇ : ∀ xs ys → ys ∈ _⊴_ xs → (xs ⊴ᵇ ys) ≡ true
⊴→⊴ᵇ xs ys =
  rec (isSetBool (xs ⊴ᵇ ys) true)
      (λ { (valxs≤valys , wgtys≤wgtxs) →
             cong₂ _and_ (≤→≤ᵇ-true valxs≤valys) (≤→≤ᵇ-true wgtys≤wgtxs) })

-- The value order, by contrast, is total, so a single comparison decides it.
-- `xs ≥ₛᵇ ys` decides `ys ∈ _≥ₛ_ xs`.
infix 4 _≥ₛᵇ_

_≥ₛᵇ_ : List Item → List Item → Bool
xs ≥ₛᵇ ys = val xs ≤ᵇ val ys

≥ₛᵇ→≥ₛ : ∀ xs ys → (xs ≥ₛᵇ ys) ≡ true → ys ∈ _≥ₛ_ xs
≥ₛᵇ→≥ₛ xs ys p = ∣ ≤ᵇ-true→≤ p ∣₁

≥ₛ→≥ₛᵇ : ∀ xs ys → ys ∈ _≥ₛ_ xs → (xs ≥ₛᵇ ys) ≡ true
≥ₛ→≥ₛᵇ xs ys = rec (isSetBool (xs ≥ₛᵇ ys) true) ≤→≤ᵇ-true

-- The side condition for step (27): dominance refines the value order,
-- i.e. v ⊵ a implies v ⪰ a. Only the value component survives; the weight
-- component is discarded. This is why maximising by value over a thinned
-- set still maximises by value over the whole set.
⊴-⊆-≥ₛ : ∀ a v → v ∈ _⊴_ a → v ∈ _≥ₛ_ a
⊴-⊆-≥ₛ a v = PT.map fst

-- `subsw cap x` is monotonic on dominance. Both `val` and `wgt` are folds that
-- add the new item's own value/weight on the front, so consing x preserves
-- both components -- and because x ∷ v is no heavier than x ∷ u, it survives
-- the capacity filter whenever x ∷ u does. This is `Monotonic (subsw cap)`
-- from the ThinT record, unfolded so it need not sit under a ThinT instance.
subsw-monotonic : ∀ cap x v u → v ∈ _⊴_ u → ∀ z → z ∈ subsw cap x u
                → ∥ Σ (List Item) (λ z' → (z' ∈ subsw cap x v) × (z' ∈ _⊴_ z)) ∥₁
subsw-monotonic cap x v u v⊵u z z∈ = rec squash₁ helper z∈
  where
    helper : (z ∈ return u) ⊎ (z ∈ filt (withinW cap) (x ∷ u))
           → ∥ Σ (List Item) (λ z' → (z' ∈ subsw cap x v) × (z' ∈ _⊴_ z)) ∥₁

    -- z is u itself: v already dominates it, and v ∈ subsw cap x v.
    helper (_⊎_.inl z∈ret) =
      rec squash₁
        (λ u≡z → ∣ v , ∣ _⊎_.inl (y∈[y] v) ∣₁ , subst (λ t → v ∈ _⊴_ t) u≡z v⊵u ∣₁)
        z∈ret

    -- z is x ∷ u, kept by the filter; match it with x ∷ v.
    helper (_⊎_.inr z∈filt) with withinW cap (x ∷ u) | inspect (withinW cap) (x ∷ u)
    ... | false | _       = rec* z∈filt
    ... | true  | [ eq ]ᵢ =
      rec squash₁
        (λ { (valu≤valv , wgtv≤wgtu) →
          rec squash₁
            (λ x∷u≡z →
              let x∷v≤cap : wgt (x ∷ v) ≤ cap
                  x∷v≤cap = ≤-trans (≤-k+ wgtv≤wgtu) (≤ᵇ-true→≤ eq)

                  x∷v∈filt : (x ∷ v) ∈ filt (withinW cap) (x ∷ v)
                  x∷v∈filt = subst (λ S → (x ∷ v) ∈ S)
                               (sym (filt-true (withinW cap) (x ∷ v) (≤→≤ᵇ-true x∷v≤cap)))
                               (y∈[y] (x ∷ v))
              in ∣ x ∷ v
                 , ∣ _⊎_.inr x∷v∈filt ∣₁
                 , subst (λ t → (x ∷ v) ∈ _⊴_ t) x∷u≡z
                     ∣ ≤-k+ valu≤valv , ≤-k+ wgtv≤wgtu ∣₁
                 ∣₁)
            z∈filt })
        v⊵u
