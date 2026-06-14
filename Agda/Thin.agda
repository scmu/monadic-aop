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
    -- (`t ∈ h x` is a subset `t ⊆ A`, and its members are just its elements).
    -- (∀ x t → t ∈ h x → t ⊆ f x) means subsets of h are contained in f

    universal-property-func-⇒ : {X : Type ℓ} (f : X → ℙ A) (h : X → ℙ (ℙ A))
                              → h ⊑ (thin ∘ f)
                              → (∀ x t → t ∈ h x → t ⊆ f x) ×
                                (∀ x t y0 → t ∈ h x → y0 ∈ f x → ∥ Σ A (λ y1 → (y1 ∈ t) × (y1 ∈ Q y0)) ∥₁)
    universal-property-func-⇐ : {X : Type ℓ} (f : X → ℙ A) (h : X → ℙ (ℙ A))
                              → (∀ x t → t ∈ h x → t ⊆ f x) ×
                                (∀ x t y0 → t ∈ h x → y0 ∈ f x → ∥ Σ A (λ y1 → (y1 ∈ t) × (y1 ∈ Q y0)) ∥₁)
                              → h ⊑ (thin ∘ f)

  thin-universal-property-set-⇒ : (xs ys : ℙ A) → ys ∈ thin xs → (ys ⊆ xs) ×
                        (∀ x → x ∈ xs → ∥ Σ A (λ y → (y ∈ ys) × (y ∈ Q x)) ∥₁)
  thin-universal-property-set-⇒ xs ys ys∈thin = p1 , p2
    where
      hyp : (const {X = Unit*} (return ys)) ⊑ (thin ∘ const xs)
      hyp _ = elem_subset_singleton (thin xs) ys ys∈thin

      props = universal-property-func-⇒ {X = Unit*} (const xs) (const (return ys)) hyp

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
      ret-ys⊆thin-xs = universal-property-func-⇐ {X = Unit*} (const xs) (const (return ys)) (cond1 , cond2) tt*
