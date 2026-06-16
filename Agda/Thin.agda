{-# OPTIONS --cubical #-}
module Thin where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Cubical.Data.Sigma.Base using (_×_; Σ; Σ-syntax) 
open import Cubical.Data.Sum.Base using (_⊎_) 
open import Cubical.Data.Int
open import Cubical.Data.List hiding (rec)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty using (isProp⊥; isProp⊥* ; ⊥* ; elim*; ⊥)
open import Cubical.Data.Unit using (Unit*; tt*)

open import Monad_v2
open import MonadicList 
open import Sets 
open import Reasoning 

private 
  variable
    ℓ : Level

record ThinQ {ℓ : Level} {A : Type ℓ} (Q : A → ℙ A) : Type (ℓ-suc (ℓ-suc ℓ)) where
  field
    thin : ℙ A → ℙ (ℙ A)

    -- Let T = ℙ, so `mem = collect = id`
    -- (∀ x t → t ∈ h x → t ⊆ f x) means subsets of h are contained in f

    thin-universal-property-func-⇒ : {X : Type ℓ} (f : X → ℙ A) (h : X → ℙ (ℙ A))
                              → h ⊑ (thin ∘ f)
                              → (∀ x t → t ∈ h x → t ⊆ f x) ×
                                (∀ x t y0 → t ∈ h x → y0 ∈ f x → ∥ Σ A (λ y1 → (y1 ∈ t) × (y1 ∈ Q y0)) ∥₁)
    thin-universal-property-func-⇐ : {X : Type ℓ} (f : X → ℙ A) (h : X → ℙ (ℙ A))
                              → (∀ x t → t ∈ h x → t ⊆ f x) ×
                                (∀ x t y0 → t ∈ h x → y0 ∈ f x → ∥ Σ A (λ y1 → (y1 ∈ t) × (y1 ∈ Q y0)) ∥₁)
                              → h ⊑ (thin ∘ f)

  thin-universal-property-set-⇒ : (xs ys : ℙ A) → ys ∈ thin xs → (ys ⊆ xs) ×
                        (∀ x → x ∈ xs → ∥ Σ A (λ y → (y ∈ ys) × (y ∈ Q x)) ∥₁)
  thin-universal-property-set-⇒ xs ys ys∈thin = p1 , p2
    where
      hyp : (const {X = Unit*} (return ys)) ⊑ (thin ∘ const xs)
      hyp _ = elem_subset_singleton (thin xs) ys ys∈thin

      props = thin-universal-property-func-⇒ {X = Unit*} (const xs) (const (return ys)) hyp

      p1 : ys ⊆ xs
      p1 = fst props tt* ys (y∈[y] ys)

      p2 : ∀ x → x ∈ xs → ∥ Σ A (λ y → (y ∈ ys) × (y ∈ Q x)) ∥₁
      p2 x x∈xs = snd props tt* ys x (y∈[y] ys) x∈xs

  thin-universal-property-set-⇐ : (xs ys : ℙ A) → (ys ⊆ xs) ×
                  (∀ x → x ∈ xs → ∥ Σ A (λ y → (y ∈ ys) × (y ∈ Q x)) ∥₁) → ys ∈ thin xs
  thin-universal-property-set-⇐ xs ys (ys⊆xs , q) = singleton_sub_elem (thin xs) ys ret-ys⊆thin-xs
    where
      cond1 : (u : Unit*) (t : ℙ A) → t ∈ return ys → t ⊆ xs
      cond1 _ t t∈ret a a∈t =
        rec (P.∈-isProp xs a) (λ ys≡t → ys⊆xs a (subst (λ w → a ∈ w) (sym ys≡t) a∈t)) t∈ret

      cond2 : (u : Unit*) (t : ℙ A) (y0 : A) → t ∈ return ys → y0 ∈ xs
            → ∥ Σ A (λ y1 → (y1 ∈ t) × (y1 ∈ Q y0)) ∥₁
      cond2 _ t y0 t∈ret y0∈xs =
        rec squash₁ (λ ys≡t → subst (λ w → ∥ Σ A (λ y1 → (y1 ∈ w) × (y1 ∈ Q y0)) ∥₁) ys≡t (q y0 y0∈xs)) t∈ret

      ret-ys⊆thin-xs : return ys ⊆ thin xs
      ret-ys⊆thin-xs = thin-universal-property-func-⇐ {X = Unit*} (const xs) (const (return ys)) (cond1 , cond2) tt*

  -- `f x` is monotonic on (⪰) for all x, where `y ∈ Q x` reads as `y ⪰ x`.
  -- This is exactly the monotonicity assumption of the Thinning Theorem
  -- (paper Appendix A, the `{- monotonicity -}` step): if v ⪰ w, then any
  -- result z of stepping w is matched by some result z' of stepping v with z' ⪰ z.
  Monotonic : {X : Type ℓ} → (f : X → A → ℙ A) → Type ℓ
  Monotonic {X} f = ∀ x v w → v ∈ Q w → ∀ z → z ∈ f x w
                  → ∥ Σ A (λ z' → (z' ∈ f x v) × (z' ∈ Q z)) ∥₁

  thin-cancel : {X : Type ℓ} (f : X → ℙ A) →
    (x : X) (t : ℙ A) (y0 : A)
    → t ∈ (thin ∘ f) x 
    → y0 ∈ f x → ∥ Σ A (λ y1 → (y1 ∈ t) × (y1 ∈ Q y0)) ∥₁
  thin-cancel {X} f = snd (thin-universal-property-func-⇒ {X} f (thin ∘ f) (⊑-refl (thin ∘ f)))
  
  thinning-thm : {X : Type ℓ}
    → (f : X → A → ℙ A) → (e : ℙ A)
    → R-trans Q
    → Monotonic f
    → foldrM (λ x → thin ∘ (λ s → f x =<< s)) (thin e) ⊑ thin ∘ foldrM f e
  thinning-thm {X} f e Qt fm [] = λ t t∈ → t∈
  thinning-thm {X} f e Qt fm (x ∷ xs) = reasoning⊆ (
    ⊆begin
      foldrM (λ x → thin ∘ (λ s → f x =<< s)) (thin e) (x ∷ xs)

    -- definition of foldrM
    ≡⟨ refl ⟩⊆
      (thin ∘ (λ s → f x =<< s)) =<< foldrM (λ x → thin ∘ (λ s → f x =<< s)) (thin e) xs

    -- induction hypothesis, under (thin ∘ (f x =<<_)) =<<_
    ⊆⟨ incl (=<<-monotonic-right (thin ∘ (λ s → f x =<< s))
               (foldrM (λ x → thin ∘ (λ s → f x =<< s)) (thin e) xs)
               (thin (foldrM f e xs))
               (thinning-thm {X} f e Qt fm xs)) ⟩
      (thin ∘ (λ s → f x =<< s)) =<< thin (foldrM f e xs)

    -- fusion: thin absorbs the inner (f x =<<_) ∘ thin
    ⊆⟨ incl (lem x (foldrM f e xs)) ⟩
      thin (f x =<< foldrM f e xs)

    -- definition of foldrM
    ≡⟨ refl ⟩⊆
      (thin ∘ foldrM f e) (x ∷ xs)

    ⊆∎)
    where
      -- Every t produced by thinning after one more step (over thinned inputs) 
      -- is itself a valid thinning of the full one-step result `f x' =<< m`.
      lem : ∀ x' (m : ℙ A)
          → ((thin ∘ (λ s → f x' =<< s)) =<< thin m) ⊆ thin (f x' =<< m)
      lem x' m t t∈ = rec (P.∈-isProp (thin (f x' =<< m)) t) helper t∈
        where
          helper : Σ (ℙ A) (λ u → (u ∈ thin m) × (t ∈ thin (f x' =<< u)))
                 → t ∈ thin (f x' =<< m)
          helper (u , u∈thin-m , t∈thin-f-u) =
            thin-universal-property-set-⇐ (f x' =<< m) t (cond-a , cond-b)
            where
              u⊆m : u ⊆ m
              u⊆m = fst (thin-universal-property-set-⇒ m u u∈thin-m)

              -- every member of m is dominated by some member of u
              u-dom : ∀ w → w ∈ m → ∥ Σ A (λ v → (v ∈ u) × (v ∈ Q w)) ∥₁
              u-dom = snd (thin-universal-property-set-⇒ m u u∈thin-m)

              -- every member of (f x' =<< u) is dominated by some member of t
              t-dom : ∀ z → z ∈ (f x' =<< u) → ∥ Σ A (λ y → (y ∈ t) × (y ∈ Q z)) ∥₁
              t-dom = snd (thin-universal-property-set-⇒ (f x' =<< u) t t∈thin-f-u)

              -- (a) t ⊆ f x' =<< u ⊆ f x' =<< m
              cond-a : t ⊆ (f x' =<< m)
              cond-a = P.⊆-trans t (f x' =<< u) (f x' =<< m)
                         (fst (thin-universal-property-set-⇒ (f x' =<< u) t t∈thin-f-u))
                         (=<<-⊆-right u m (f x') u⊆m)

              -- (b) every member of (f x' =<< m) is dominated by some member of t,
              cond-b : ∀ z → z ∈ (f x' =<< m) → ∥ Σ A (λ y → (y ∈ t) × (y ∈ Q z)) ∥₁
              cond-b z z∈fm = rec squash₁ cond-b-helper z∈fm
                where
                  cond-b-helper : Σ A (λ w → (w ∈ m) × (z ∈ f x' w))
                                → ∥ Σ A (λ y → (y ∈ t) × (y ∈ Q z)) ∥₁
                  cond-b-helper (w , w∈m , z∈fw) =
                    rec squash₁
                      (λ { (v , v∈u , v∈Qw) →
                        rec squash₁
                          (λ { (z' , z'∈fv , z'∈Qz) →
                            rec squash₁
                              (λ { (y , y∈t , y∈Qz') →
                                ∣ y , y∈t , Qt z z' y z'∈Qz y∈Qz' ∣₁ })
                              (t-dom z' ∣ v , v∈u , z'∈fv ∣₁) })
                          (fm x' v w v∈Qw z z∈fw) })
                      (u-dom w w∈m)
