{-# OPTIONS --cubical --guardedness #-}
-- The concrete algorithm: thinmerge, add, and everything true of them.
-- None of this mentions the abstract `thin`, so it needs no ThinT instance --
module Examples.Knapsack.Impl where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path using (inspect; [_]ᵢ)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Cubical.Data.Sigma.Base using (_×_; Σ)
open import Cubical.Data.Sum.Base using (_⊎_)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order as Order using (_≤_; ≤-refl; ≤-trans; ≤-k+; <-weaken; isProp≤)
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)
open import Cubical.Data.List hiding (rec; foldr; map)
open import Cubical.Data.Empty using (elim*; ⊥; rec*)
open import Cubical.Data.Unit using (Unit; tt)
import Cubical.Data.Empty

open import Monad_v2
open import Min
open import MonadicList
open import Sets
open import NatBool
import ThinT as Thinning
open Thinning using (T; mem; collect; collect-∅; collect-ret; collect-∪; mergeT)
open import Examples.Knapsack.Base
open import Examples.Knapsack.Order

-- [ The invariant that makes `head` a maximum ]

-- Every member of t has value at most val b.
Below : List Item → T (List Item) → Type ℓ-zero
Below b t = ∀ a → a ∈ mem t → val a ≤ val b

-- Candidate lists are kept in descending value order, so the head is the best.
Sorted : T (List Item) → Type ℓ-zero
Sorted []      = Unit
Sorted (b ∷ t) = Below b t × Sorted t

NonEmpty : T (List Item) → Type ℓ-zero
NonEmpty []      = ⊥
NonEmpty (_ ∷ _) = Unit

-- A sorted non-empty list's head is a ⪰-maximum of its members.
sorted-head-max : ∀ t → NonEmpty t → Sorted t → return (head t) ⊆ minR (mem t)
sorted-head-max (b ∷ t) _ (below , _) =
  set-property-⇐ (mem (b ∷ t)) (return b)
    (elem_subset_singleton (mem (b ∷ t)) b ∣ _⊎_.inl (y∈[y] b) ∣₁)
    best
  where
    best : ∀ y → y ∈ return b → ∀ a → a ∈ mem (b ∷ t) → y ∈ _≥ₛ_ a
    best y y∈ret a a∈ =
      rec squash₁
        (λ b≡y → rec squash₁
          (λ { (_⊎_.inl b≡a) → rec squash₁ (λ eq → ∣ subst (λ z → val z ≤ val y) eq
                                                       (subst (λ z → val b ≤ val z) b≡y ≤-refl) ∣₁) b≡a
             ; (_⊎_.inr a∈t) → ∣ subst (λ z → val a ≤ val z) b≡y (below a a∈t) ∣₁ }) a∈)
        y∈ret

-- "some survivor v of r dominates a"
Dom : T (List Item) → List Item → Type ℓ-zero
Dom r a = ∥ Σ (List Item) (λ v → (v ∈ mem r) × (v ∈ _⊴_ a)) ∥₁

thinmerge : T (List Item) → T (List Item) → T (List Item)
thinmerge [] u = u
thinmerge t [] = t
thinmerge (xs ∷ t) (ys ∷ u) =
  if wgt ys <ᵇ wgt xs                              -- xs heavier than ys
  then (if val xs ≤ᵇ val ys
        then thinmerge t (ys ∷ u)                  -- ys dominates xs: drop xs
        else xs ∷ thinmerge t (ys ∷ u))            -- incomparable: xs first
  else if wgt xs <ᵇ wgt ys                         -- xs lighter than ys
  then (if val xs <ᵇ val ys
        then ys ∷ thinmerge (xs ∷ t) u             -- incomparable: ys first
        else thinmerge (xs ∷ t) u)                 -- xs dominates ys: drop ys
  else (if val xs <ᵇ val ys                        -- equal weight
        then thinmerge t (ys ∷ u)                  -- ys dominates xs: drop xs
        else thinmerge (xs ∷ t) u)                 -- xs dominates ys: drop ys

add : Wgt → Item → T (List Item) → T (List Item)
add w x t = collect ((filt (withinW w) ∘ (_∷_ x)) =<< mem t)

-- (a) every survivor of thinmerge came from one of its two inputs.
thinmerge-⊆ : ∀ p q → mem (thinmerge p q) ⊆ (mem p ∪ mem q)
thinmerge-⊆ [] q = ⊆-∪-right (mem []) (mem q)
thinmerge-⊆ (xs ∷ p) [] = ⊆-∪-left (mem (xs ∷ p)) (mem [])
-- The two recursive calls are made here, in the clause body, and passed in:
-- inside a `where` the termination checker loses the lexicographic descent.
thinmerge-⊆ (xs ∷ p) (ys ∷ q) = go (thinmerge-⊆ p (ys ∷ q)) (thinmerge-⊆ (xs ∷ p) q)
  where
    G : T (List Item) → Type ℓ-zero
    G r = mem r ⊆ (mem (xs ∷ p) ∪ mem (ys ∷ q))

    IHL = mem (thinmerge p (ys ∷ q)) ⊆ (mem p ∪ mem (ys ∷ q))
    IHR = mem (thinmerge (xs ∷ p) q) ⊆ (mem (xs ∷ p) ∪ mem q)

    dropL : IHL → G (thinmerge p (ys ∷ q))
    dropL ih = P.⊆-trans (mem (thinmerge p (ys ∷ q))) (mem p ∪ mem (ys ∷ q))
                         (mem (xs ∷ p) ∪ mem (ys ∷ q)) ih
                 (⊆-∪-monotonic-left (mem p) (mem (xs ∷ p)) (mem (ys ∷ q))
                   (⊆-∪-right (return xs) (mem p)))

    keepL : IHL → G (xs ∷ thinmerge p (ys ∷ q))
    keepL ih = ∪-⊆-both (return xs) (mem (thinmerge p (ys ∷ q)))
                        (mem (xs ∷ p) ∪ mem (ys ∷ q))
                 (P.⊆-trans (return xs) (mem (xs ∷ p)) (mem (xs ∷ p) ∪ mem (ys ∷ q))
                    (⊆-∪-left (return xs) (mem p))
                    (⊆-∪-left (mem (xs ∷ p)) (mem (ys ∷ q))))
                 (dropL ih)

    dropR : IHR → G (thinmerge (xs ∷ p) q)
    dropR ih = P.⊆-trans (mem (thinmerge (xs ∷ p) q)) (mem (xs ∷ p) ∪ mem q)
                         (mem (xs ∷ p) ∪ mem (ys ∷ q)) ih
                 (⊆-∪-monotonic-right (mem q) (mem (ys ∷ q)) (mem (xs ∷ p))
                   (⊆-∪-right (return ys) (mem q)))

    keepR : IHR → G (ys ∷ thinmerge (xs ∷ p) q)
    keepR ih = ∪-⊆-both (return ys) (mem (thinmerge (xs ∷ p) q))
                        (mem (xs ∷ p) ∪ mem (ys ∷ q))
                 (P.⊆-trans (return ys) (mem (ys ∷ q)) (mem (xs ∷ p) ∪ mem (ys ∷ q))
                    (⊆-∪-left (return ys) (mem q))
                    (⊆-∪-right (mem (xs ∷ p)) (mem (ys ∷ q))))
                 (dropR ih)

    go : IHL → IHR → G (thinmerge (xs ∷ p) (ys ∷ q))
    go ihL ihR =
      if-split G (wgt ys <ᵇ wgt xs)
        (λ _ → if-split G (val xs ≤ᵇ val ys) (λ _ → dropL ihL) (λ _ → keepL ihL))
        (λ _ → if-split G (wgt xs <ᵇ wgt ys)
                 (λ _ → if-split G (val xs <ᵇ val ys) (λ _ → keepR ihR) (λ _ → dropR ihR))
                 (λ _ → if-split G (val xs <ᵇ val ys) (λ _ → dropL ihL) (λ _ → dropR ihR)))

-- (b) every candidate in either input is dominated by some survivor.
thinmerge-dom : ∀ p q a → a ∈ (mem p ∪ mem q) → Dom (thinmerge p q) a
thinmerge-dom [] q a a∈ =
  rec squash₁ (λ { (_⊎_.inl a∈∅) → elim* a∈∅
                 ; (_⊎_.inr a∈q) → ∣ a , a∈q , ⊴-refl a ∣₁ }) a∈
thinmerge-dom (xs ∷ p) [] a a∈ =
  rec squash₁ (λ { (_⊎_.inl a∈L) → ∣ a , a∈L , ⊴-refl a ∣₁
                 ; (_⊎_.inr a∈∅) → elim* a∈∅ }) a∈
thinmerge-dom (xs ∷ p) (ys ∷ q) = go (thinmerge-dom p (ys ∷ q)) (thinmerge-dom (xs ∷ p) q)
  where
    G : T (List Item) → Type ℓ-zero
    G r = ∀ a → a ∈ (mem (xs ∷ p) ∪ mem (ys ∷ q)) → Dom r a

    IHL = ∀ a → a ∈ (mem p ∪ mem (ys ∷ q)) → Dom (thinmerge p (ys ∷ q)) a
    IHR = ∀ a → a ∈ (mem (xs ∷ p) ∪ mem q) → Dom (thinmerge (xs ∷ p) q) a

    -- keep xs: the IH's witness survives, and xs vouches for itself
    keepL : IHL → G (xs ∷ thinmerge p (ys ∷ q))
    keepL ih a a∈ = rec squash₁ handle a∈
      where
        up : Dom (thinmerge p (ys ∷ q)) a → Dom (xs ∷ thinmerge p (ys ∷ q)) a
        up = rec squash₁ (λ { (v , v∈ , v⊵a) → ∣ v , ∣ _⊎_.inr v∈ ∣₁ , v⊵a ∣₁ })

        handle : (a ∈ mem (xs ∷ p)) ⊎ (a ∈ mem (ys ∷ q)) → Dom (xs ∷ thinmerge p (ys ∷ q)) a
        handle (_⊎_.inr a∈R) = up (ih a ∣ _⊎_.inr a∈R ∣₁)
        handle (_⊎_.inl a∈L) =
          rec squash₁ (λ { (_⊎_.inl xs≡a) →
                             rec squash₁ (λ eq →
                               ∣ xs , ∣ _⊎_.inl (y∈[y] xs) ∣₁
                                     , subst (λ z → xs ∈ _⊴_ z) eq (⊴-refl xs) ∣₁) xs≡a
                         ; (_⊎_.inr a∈p) → up (ih a ∣ _⊎_.inl a∈p ∣₁) }) a∈L

    -- drop xs: legitimate because ys dominates it, so a survivor dominating
    -- ys dominates xs too (⊴-trans)
    dropL : (ys ∈ _⊴_ xs) → IHL → G (thinmerge p (ys ∷ q))
    dropL ys⊵xs ih a a∈ = rec squash₁ handle a∈
      where
        handle : (a ∈ mem (xs ∷ p)) ⊎ (a ∈ mem (ys ∷ q)) → Dom (thinmerge p (ys ∷ q)) a
        handle (_⊎_.inr a∈R) = ih a ∣ _⊎_.inr a∈R ∣₁
        handle (_⊎_.inl a∈L) =
          rec squash₁ (λ { (_⊎_.inl xs≡a) →
                             rec squash₁ (λ eq →
                               rec squash₁ (λ { (v , v∈ , v⊵ys) →
                                 ∣ v , v∈ , subst (λ z → v ∈ _⊴_ z) eq
                                              (⊴-trans v ys xs v⊵ys ys⊵xs) ∣₁ })
                                 (ih ys ∣ _⊎_.inr ∣ _⊎_.inl (y∈[y] ys) ∣₁ ∣₁)) xs≡a
                         ; (_⊎_.inr a∈p) → ih a ∣ _⊎_.inl a∈p ∣₁ }) a∈L

    keepR : IHR → G (ys ∷ thinmerge (xs ∷ p) q)
    keepR ih a a∈ = rec squash₁ handle a∈
      where
        up : Dom (thinmerge (xs ∷ p) q) a → Dom (ys ∷ thinmerge (xs ∷ p) q) a
        up = rec squash₁ (λ { (v , v∈ , v⊵a) → ∣ v , ∣ _⊎_.inr v∈ ∣₁ , v⊵a ∣₁ })

        handle : (a ∈ mem (xs ∷ p)) ⊎ (a ∈ mem (ys ∷ q)) → Dom (ys ∷ thinmerge (xs ∷ p) q) a
        handle (_⊎_.inl a∈L) = up (ih a ∣ _⊎_.inl a∈L ∣₁)
        handle (_⊎_.inr a∈R) =
          rec squash₁ (λ { (_⊎_.inl ys≡a) →
                             rec squash₁ (λ eq →
                               ∣ ys , ∣ _⊎_.inl (y∈[y] ys) ∣₁
                                     , subst (λ z → ys ∈ _⊴_ z) eq (⊴-refl ys) ∣₁) ys≡a
                         ; (_⊎_.inr a∈q) → up (ih a ∣ _⊎_.inr a∈q ∣₁) }) a∈R

    dropR : (xs ∈ _⊴_ ys) → IHR → G (thinmerge (xs ∷ p) q)
    dropR xs⊵ys ih a a∈ = rec squash₁ handle a∈
      where
        handle : (a ∈ mem (xs ∷ p)) ⊎ (a ∈ mem (ys ∷ q)) → Dom (thinmerge (xs ∷ p) q) a
        handle (_⊎_.inl a∈L) = ih a ∣ _⊎_.inl a∈L ∣₁
        handle (_⊎_.inr a∈R) =
          rec squash₁ (λ { (_⊎_.inl ys≡a) →
                             rec squash₁ (λ eq →
                               rec squash₁ (λ { (v , v∈ , v⊵xs) →
                                 ∣ v , v∈ , subst (λ z → v ∈ _⊴_ z) eq
                                              (⊴-trans v xs ys v⊵xs xs⊵ys) ∣₁ })
                                 (ih xs ∣ _⊎_.inl ∣ _⊎_.inl (y∈[y] xs) ∣₁ ∣₁)) ys≡a
                         ; (_⊎_.inr a∈q) → ih a ∣ _⊎_.inr a∈q ∣₁ }) a∈R

    -- the six guards, each supplying the ordering fact its branch needs
    go : IHL → IHR → G (thinmerge (xs ∷ p) (ys ∷ q))
    go ihL ihR =
      if-split G (wgt ys <ᵇ wgt xs)
        (λ e1 → if-split G (val xs ≤ᵇ val ys)
                  (λ e3 → dropL ∣ ≤ᵇ-true→≤ e3 , <-weaken (<ᵇ-true→< e1) ∣₁ ihL)
                  (λ _  → keepL ihL))
        (λ e1 → if-split G (wgt xs <ᵇ wgt ys)
                  (λ e2 → if-split G (val xs <ᵇ val ys)
                            (λ _  → keepR ihR)
                            (λ e4 → dropR ∣ ≮→≥ (<ᵇ-false→≮ e4)
                                          , <-weaken (<ᵇ-true→< e2) ∣₁ ihR))
                  (λ e2 → if-split G (val xs <ᵇ val ys)
                            (λ e4 → dropL ∣ <-weaken (<ᵇ-true→< e4)
                                          , ≮→≥ (<ᵇ-false→≮ e2) ∣₁ ihL)
                            (λ e4 → dropR ∣ ≮→≥ (<ᵇ-false→≮ e4)
                                          , ≮→≥ (<ᵇ-false→≮ e1) ∣₁ ihR)))

-- [ thinmerge preserves the invariant ]

thinmerge-NE : ∀ p q → (NonEmpty p ⊎ NonEmpty q) → NonEmpty (thinmerge p q)
thinmerge-NE [] q (_⊎_.inl ne) = Cubical.Data.Empty.rec ne
thinmerge-NE [] q (_⊎_.inr ne) = ne
thinmerge-NE (xs ∷ p) [] _ = tt
thinmerge-NE (xs ∷ p) (ys ∷ q) _ =
  go (thinmerge-NE p (ys ∷ q) (_⊎_.inr tt)) (thinmerge-NE (xs ∷ p) q (_⊎_.inl tt))
  where
    go : NonEmpty (thinmerge p (ys ∷ q)) → NonEmpty (thinmerge (xs ∷ p) q)
       → NonEmpty (thinmerge (xs ∷ p) (ys ∷ q))
    go nl nr =
      if-split NonEmpty (wgt ys <ᵇ wgt xs)
        (λ _ → if-split NonEmpty (val xs ≤ᵇ val ys) (λ _ → nl) (λ _ → tt))
        (λ _ → if-split NonEmpty (wgt xs <ᵇ wgt ys)
                 (λ _ → if-split NonEmpty (val xs <ᵇ val ys) (λ _ → tt) (λ _ → nr))
                 (λ _ → if-split NonEmpty (val xs <ᵇ val ys) (λ _ → nl) (λ _ → nr)))

thinmerge-Sorted : ∀ p q → Sorted p → Sorted q → Sorted (thinmerge p q)
thinmerge-Sorted [] q _ sq = sq
thinmerge-Sorted (xs ∷ p) [] sp _ = sp
thinmerge-Sorted (xs ∷ p) (ys ∷ q) (belowXs , sp) (belowYs , sq) =
  go (thinmerge-Sorted p (ys ∷ q) sp (belowYs , sq))
     (thinmerge-Sorted (xs ∷ p) q (belowXs , sp) sq)
  where
    -- thinmerge-⊆ bounds the survivors by the two inputs, which the
    -- sortedness of those inputs then bounds by xs (resp. ys).
    belowL : val ys ≤ val xs → Below xs (thinmerge p (ys ∷ q))
    belowL vy≤vx a a∈ =
      rec isProp≤
        (λ { (_⊎_.inl a∈p) → belowXs a a∈p
           ; (_⊎_.inr a∈R) →
               rec isProp≤
                 (λ { (_⊎_.inl ys≡a) →
                        rec isProp≤ (λ eq → subst (λ z → val z ≤ val xs) eq vy≤vx) ys≡a
                    ; (_⊎_.inr a∈q) → ≤-trans (belowYs a a∈q) vy≤vx }) a∈R })
        (thinmerge-⊆ p (ys ∷ q) a a∈)

    belowR : val xs ≤ val ys → Below ys (thinmerge (xs ∷ p) q)
    belowR vx≤vy a a∈ =
      rec isProp≤
        (λ { (_⊎_.inl a∈L) →
               rec isProp≤
                 (λ { (_⊎_.inl xs≡a) →
                        rec isProp≤ (λ eq → subst (λ z → val z ≤ val ys) eq vx≤vy) xs≡a
                    ; (_⊎_.inr a∈p) → ≤-trans (belowXs a a∈p) vx≤vy }) a∈L
           ; (_⊎_.inr a∈q) → belowYs a a∈q })
        (thinmerge-⊆ (xs ∷ p) q a a∈)

    go : Sorted (thinmerge p (ys ∷ q)) → Sorted (thinmerge (xs ∷ p) q)
       → Sorted (thinmerge (xs ∷ p) (ys ∷ q))
    go sl sr =
      if-split Sorted (wgt ys <ᵇ wgt xs)
        (λ _ → if-split Sorted (val xs ≤ᵇ val ys)
                 (λ _  → sl)
                 (λ e3 → belowL (≰→≥ (≤ᵇ-false→≰ e3)) , sl))
        (λ _ → if-split Sorted (wgt xs <ᵇ wgt ys)
                 (λ _ → if-split Sorted (val xs <ᵇ val ys)
                          (λ e4 → belowR (<-weaken (<ᵇ-true→< e4)) , sr)
                          (λ _  → sr))
                 (λ _ → if-split Sorted (val xs <ᵇ val ys) (λ _ → sl) (λ _ → sr)))

-- [ add preserves the invariant ]

-- `add` goes through the postulated `collect`, but the three collect laws
-- determine it completely: mem t is a ∪ of returns, and filt is return or ∅.
add-[] : ∀ w x → add w x [] ≡ []
add-[] w x = cong collect (=<<-∅ (filt (withinW w) ∘ (_∷_ x))) ∙ collect-∅

add-∷ : ∀ w x ys t
      → add w x (ys ∷ t) ≡ mergeT (collect (filt (withinW w) (x ∷ ys))) (add w x t)
add-∷ w x ys t =
  cong collect (=<<-∪-dist-left f (return ys) (mem t)
                ∙ cong (λ S → S ∪ (f =<< mem t)) (ret-left-id ys f))
  ∙ collect-∪ (f ys) (f =<< mem t)
  where f = filt (withinW w) ∘ (_∷_ x)

add-∷-true : ∀ w x ys t → withinW w (x ∷ ys) ≡ true
           → add w x (ys ∷ t) ≡ (x ∷ ys) ∷ add w x t
add-∷-true w x ys t eq =
  add-∷ w x ys t
  ∙ cong (λ u → mergeT (collect u) (add w x t)) (filt-true (withinW w) (x ∷ ys) eq)
  ∙ cong (λ u → mergeT u (add w x t)) (collect-ret (x ∷ ys))

add-∷-false : ∀ w x ys t → withinW w (x ∷ ys) ≡ false
            → add w x (ys ∷ t) ≡ add w x t
add-∷-false w x ys t eq =
  add-∷ w x ys t
  ∙ cong (λ u → mergeT (collect u) (add w x t)) (filt-false (withinW w) (x ∷ ys) eq)
  ∙ cong (λ u → mergeT u (add w x t)) collect-∅

-- consing x adds fst x to every value, so it is monotone: bounds survive
add-Below : ∀ w x b t → Below b t → Below (x ∷ b) (add w x t)
add-Below w x b [] _ =
  subst (Below (x ∷ b)) (sym (add-[] w x)) (λ a a∈ → elim* a∈)
add-Below w x b (ys ∷ t) below =
  bool-split (withinW w (x ∷ ys)) (Below (x ∷ b) (add w x (ys ∷ t)))
    (λ eq → subst (Below (x ∷ b)) (sym (add-∷-true w x ys t eq)) keep)
    (λ eq → subst (Below (x ∷ b)) (sym (add-∷-false w x ys t eq)) rest)
  where
    rest : Below (x ∷ b) (add w x t)
    rest = add-Below w x b t (λ a a∈ → below a ∣ _⊎_.inr a∈ ∣₁)

    keep : Below (x ∷ b) ((x ∷ ys) ∷ add w x t)
    keep a a∈ =
      rec isProp≤
        (λ { (_⊎_.inl x∷ys≡a) →
               rec isProp≤ (λ eq → subst (λ z → val z ≤ val (x ∷ b)) eq
                                     (≤-k+ (below ys ∣ _⊎_.inl (y∈[y] ys) ∣₁))) x∷ys≡a
           ; (_⊎_.inr a∈add) → rest a a∈add }) a∈

add-Sorted : ∀ w x t → Sorted t → Sorted (add w x t)
add-Sorted w x [] _ = subst Sorted (sym (add-[] w x)) tt
add-Sorted w x (ys ∷ t) (belowYs , st) =
  bool-split (withinW w (x ∷ ys)) (Sorted (add w x (ys ∷ t)))
    (λ eq → subst Sorted (sym (add-∷-true w x ys t eq))
              (add-Below w x ys t belowYs , add-Sorted w x t st))
    (λ eq → subst Sorted (sym (add-∷-false w x ys t eq)) (add-Sorted w x t st))

-- [ the fold maintains both ]

fold-Sorted : ∀ w xs → Sorted (foldr (λ x t → thinmerge t (add w x t)) [ [] ] xs)
fold-Sorted w [] = (λ a a∈ → elim* a∈) , tt
fold-Sorted w (x ∷ xs) =
  thinmerge-Sorted _ _ (fold-Sorted w xs) (add-Sorted w x _ (fold-Sorted w xs))

fold-NE : ∀ w xs → NonEmpty (foldr (λ x t → thinmerge t (add w x t)) [ [] ] xs)
fold-NE w [] = tt
fold-NE w (x ∷ xs) = thinmerge-NE _ _ (_⊎_.inl (fold-NE w xs))

-- The head of the fold's result is a ⪰-maximum of its members.
head-is-max : ∀ w xs
  → return (head (foldr (λ x t → thinmerge t (add w x t)) [ [] ] xs))
    ⊆ minR (mem (foldr (λ x t → thinmerge t (add w x t)) [ [] ] xs))
head-is-max w xs =
  sorted-head-max (foldr (λ x t → thinmerge t (add w x t)) [ [] ] xs)
    (fold-NE w xs) (fold-Sorted w xs)

knapsackImpl : Wgt → List Item → List Item
knapsackImpl w = head ∘ foldr (λ x t → thinmerge t (add w x t)) [ [] ]
