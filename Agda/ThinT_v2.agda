{-# OPTIONS --cubical --guardedness #-}
module ThinT_v2 where

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


T : ∀ {ℓ} → Type ℓ → Type ℓ
T = List

-- Since T is defined as List, `mem` can be defined as MonadicList's `member`.
mem : {ℓ : Level} {A : Type ℓ} → (T A) → ℙ A
mem = member

emptyT : ∀ {ℓ} {A : Type ℓ} → T A
emptyT = []

singleT : ∀ {ℓ} {A : Type ℓ} → A → T A
singleT x = x ∷ []

mergeT : ∀ {ℓ} {A : Type ℓ} → T A → T A → T A
mergeT [] ys = ys
mergeT (x ∷ xs) ys = x ∷ mergeT xs ys

mem-emptyT : ∀ {ℓ} {A : Type ℓ} → mem {ℓ} {A} emptyT ≡ ∅
mem-emptyT = refl

mem-singleT : ∀ {ℓ} {A : Type ℓ} → ∀ x → mem {ℓ} {A} (singleT x) ≡ return x
mem-singleT x = ∪-∅-unit-r (return x)

mem-mergeT : {ℓ : Level} {A : Type ℓ} (p q : T A) → mem (mergeT p q) ≡ (mem p ∪ mem q)
mem-mergeT [] q = sym (∪-∅-unit-l (mem q))
mem-mergeT (x ∷ p) q =
  (return x ∪ mem (mergeT p q))
    ≡⟨ cong (λ S → return x ∪ S) (mem-mergeT p q) ⟩
  (return x ∪ (mem p ∪ mem q))
    ≡⟨ sym (∪-assoc (return x) (mem p) (mem q)) ⟩
  ((return x ∪ mem p) ∪ mem q)
    ∎



record ThinT {ℓ : Level} {A : Type ℓ} (Q : A → ℙ A) : Type (ℓ-suc (ℓ-suc ℓ)) where
    field
        thin : ℙ A → ℙ (T A)

        thin-universal-property-func-⇒ : {X : Type ℓ} (f : X → ℙ A) (h : X → ℙ (T A))
                                → h ⊑ thin ∘ f
                                → (mem <=< h ⊑ f) ×
                                    (∀ x t₁ y₀ → t₁ ∈ h x → y₀ ∈ f x → ∥ Σ A (λ y₁ → (y₁ ∈ mem t₁) × (y₁ ∈ Q y₀)) ∥₁)
        thin-universal-property-func-⇐ : {X : Type ℓ} (f : X → ℙ A) (h : X → ℙ (T A))
                                → (mem <=< h ⊑ f) ×
                                    (∀ x t₁ y₀ → t₁ ∈ h x → y₀ ∈ f x → ∥ Σ A (λ y₁ → (y₁ ∈ mem t₁) × (y₁ ∈ Q y₀)) ∥₁)
                                → h ⊑ thin ∘ f

    -- Set-level universal property, stated directly about a set S : ℙ A.
    -- Obtained from the functional version at X = Unit*, f = const S, h = const (return u).
    thin-⇒ :
        (S : ℙ A) (u : T A)
        → u ∈ thin S
        → (mem u ⊆ S) ×
          (∀ w → w ∈ S → ∥ Σ A (λ v → (v ∈ mem u) × (v ∈ Q w)) ∥₁)
    thin-⇒ S u u∈thin = p1 , p2
        where
            hyp : const {X = Unit*} (return u) ⊑ thin ∘ const S
            hyp _ = elem_subset_singleton (thin S) u u∈thin

            props = thin-universal-property-func-⇒ {X = Unit*} (const S) (const (return u)) hyp

            p1 : mem u ⊆ S
            p1 = subst (λ V → V ⊆ S) (ret-left-id u mem) (fst props tt*)

            p2 : ∀ w → w ∈ S → ∥ Σ A (λ v → (v ∈ mem u) × (v ∈ Q w)) ∥₁
            p2 w w∈S = snd props tt* u w (y∈[y] u) w∈S

    thin-⇐ :
        (S : ℙ A) (u : T A)
        → (mem u ⊆ S) ×
          (∀ w → w ∈ S → ∥ Σ A (λ v → (v ∈ mem u) × (v ∈ Q w)) ∥₁)
        → u ∈ thin S
    thin-⇐ S u (u⊆S , q) = ret-u⊆thin-S u (y∈[y] u)
        where
            cond1 : mem <=< const {X = Unit*} (return u) ⊑ const S
            cond1 _ = subst (λ V → V ⊆ S) (sym (ret-left-id u mem)) u⊆S

            cond2 : ∀ (o : Unit*) t₁ y₀ → t₁ ∈ const (return u) o → y₀ ∈ const S o
                  → ∥ Σ A (λ y₁ → (y₁ ∈ mem t₁) × (y₁ ∈ Q y₀)) ∥₁
            cond2 _ t₁ y₀ t₁∈ret y₀∈S =
              rec squash₁ (λ u≡t₁ → subst (λ w → ∥ Σ A (λ y₁ → (y₁ ∈ mem w) × (y₁ ∈ Q y₀)) ∥₁) u≡t₁ (q y₀ y₀∈S)) t₁∈ret

            ret-u⊆thin-S : return u ⊆ thin S
            ret-u⊆thin-S =
              thin-universal-property-func-⇐ {X = Unit*} (const S) (const (return u)) (cond1 , cond2) tt*

    -- The same property for sets represented by a T-value xs, i.e. S = mem xs.
    -- Without `collect` this is just the S = mem xs instance of thin-⇒ / thin-⇐.
    thin-universal-property-set-⇒ :
        (xs ys : T A)
        → ys ∈ thin (mem xs)
        → (mem ys ⊆ mem xs) ×
          (∀ x → x ∈ mem xs → ∥ Σ A (λ y → (y ∈ mem ys) × (y ∈ Q x)) ∥₁)
    thin-universal-property-set-⇒ xs = thin-⇒ (mem xs)

    thin-universal-property-set-⇐ :
        (xs ys : T A)
        → (mem ys ⊆ mem xs) ×
          (∀ x → x ∈ mem xs → ∥ Σ A (λ y → (y ∈ mem ys) × (y ∈ Q x)) ∥₁)
        → ys ∈ thin (mem xs)
    thin-universal-property-set-⇐ xs = thin-⇐ (mem xs)

    thin-cancel : {X : Type ℓ}
        (f : X → ℙ A)
        → (x : X) (t₁ : T A) (y₀ : A)
        → t₁ ∈ (thin ∘ f) x
        → y₀ ∈ f x
        → ∥ Σ A (λ y₁ → (y₁ ∈ mem t₁) × (y₁ ∈ Q y₀)) ∥₁
    thin-cancel {X} f = snd (thin-universal-property-func-⇒ {X} f (thin ∘ f) (⊑-refl (thin ∘ f)))

    Monotonic : {X : Type ℓ} → (f : X → A → ℙ A) → Type ℓ
    Monotonic {X} f = ∀ x v w → v ∈ Q w → ∀ z → z ∈ f x w
                    → ∥ Σ A (λ z' → (z' ∈ f x v) × (z' ∈ Q z)) ∥₁

    thinning-thm : {X : Type ℓ}
      → (f : X → A → ℙ A) 
      → (e : ℙ A)
      → R-trans Q
      → Monotonic f
      → foldrM (λ x → thin ∘ f x <=< mem) (thin e) ⊑ thin ∘ foldrM f e
    thinning-thm {X} f e Qt fm [] = λ t t∈ → t∈
    thinning-thm {X} f e Qt fm (x ∷ xs) = reasoning⊆ (
      ⊆begin
        foldrM (λ x → thin ∘ f x <=< mem) (thin e) (x ∷ xs)

      -- definition of foldrM
      ≡⟨ refl ⟩⊆
        (thin ∘ (f x <=< mem)) =<< foldrM (λ x → thin ∘ f x <=< mem) (thin e) xs

      -- induction hypothesis, under (thin ∘ (f x <=< mem)) =<<_
      ⊆⟨ incl (=<<-monotonic-right (thin ∘ (f x <=< mem))
                 (foldrM (λ x → thin ∘ f x <=< mem) (thin e) xs)
                 (thin (foldrM f e xs))
                 (thinning-thm {X} f e Qt fm xs)) ⟩
        (thin ∘ (f x <=< mem)) =<< thin (foldrM f e xs)

      -- fusion: thin absorbs the inner (f x <=< mem) ∘ thin
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
            → ((thin ∘ (f x' <=< mem)) =<< thin m) ⊆ thin (f x' =<< m)
        lem x' m t t∈ = rec (P.∈-isProp (thin (f x' =<< m)) t) helper t∈
          where
            helper : Σ (T A) (λ u → (u ∈ thin m) × (t ∈ thin (f x' =<< mem u)))
                   → t ∈ thin (f x' =<< m)
            helper (u , u∈thin-m , t∈thin-f-u) =
              thin-⇐ (f x' =<< m) t (cond-a , cond-b)
              where
                u⊆m : mem u ⊆ m
                u⊆m = fst (thin-⇒ m u u∈thin-m)

                -- every member of m is dominated by some member of mem u
                u-dom : ∀ w → w ∈ m → ∥ Σ A (λ v → (v ∈ mem u) × (v ∈ Q w)) ∥₁
                u-dom = snd (thin-⇒ m u u∈thin-m)

                -- every member of (f x' =<< mem u) is dominated by some member of mem t
                t-dom : ∀ z → z ∈ (f x' =<< mem u) → ∥ Σ A (λ y → (y ∈ mem t) × (y ∈ Q z)) ∥₁
                t-dom = snd (thin-⇒ (f x' =<< mem u) t t∈thin-f-u)

                -- (a) mem t ⊆ f x' =<< mem u ⊆ f x' =<< m
                cond-a : mem t ⊆ (f x' =<< m)
                cond-a = P.⊆-trans (mem t) (f x' =<< mem u) (f x' =<< m)
                           (fst (thin-⇒ (f x' =<< mem u) t t∈thin-f-u))
                           (=<<-⊆-right (mem u) m (f x') u⊆m)

                -- (b) every member of (f x' =<< m) is dominated by some member of mem t
                cond-b : ∀ z → z ∈ (f x' =<< m) → ∥ Σ A (λ y → (y ∈ mem t) × (y ∈ Q z)) ∥₁
                cond-b z z∈fm = rec squash₁ cond-b-helper z∈fm
                  where
                    cond-b-helper : Σ A (λ w → (w ∈ m) × (z ∈ f x' w))
                                  → ∥ Σ A (λ y → (y ∈ mem t) × (y ∈ Q z)) ∥₁
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