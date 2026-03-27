{-# OPTIONS --cubical #-}
module Examples.Prefix where
    
open import Data.List hiding (foldr; head)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Cubical.Data.Sigma.Base using (_×_) 
-- open import Cubical.Functions.Logic
open import Cubical.Data.Sum.Base using (_⊎_) 
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Empty using (isProp⊥; isProp⊥* ; ⊥* ; elim*)

open import Monad_v2
open import Fold
open import Sets

private
  variable
    ℓ : Level
    X : Type ℓ  

prefix : List X → ℙ (List X) 
prefix []       = return []
prefix (x ∷ xs) = return [] ∪ (_∷_ x) <$> (prefix xs)

prefix+ : List X → ℙ (List X) 
prefix+ []       = ∅
prefix+ (x ∷ xs) = return [ x ] ∪ (_∷_ x) <$> (prefix+ xs)

suffix : List X → ℙ (List X)
suffix [] = return []
suffix (x ∷ xs) = return (x ∷ xs) ∪ suffix xs

pre : X → List X → ℙ (List X) 
pre x ys = return [] ∪ return (x ∷ ys)

pre+ : X → List X → ℙ (List X) 
pre+ x ys = return [ x ] ∪ return (x ∷ ys)

prefix' : List X → ℙ (List X) 
prefix' = foldrM pre (return [])


-- Empty list is always a prefix
nil∈prefix : ∀ {ℓ} {X : Type ℓ} → ∀ xs → [] ∈ prefix {X = X} xs
nil∈prefix [] = ∣ refl ∣₁
nil∈prefix (x ∷ xs) = ∣ _⊎_.inl ∣ refl ∣₁ ∣₁


lem : (x : X) (A : ℙ (List X)) → (return [] ∪ return [ x ]) ∪ (_∷_ x) <$> A ≡ (return [] ∪ return [ x ]) ∪ pre x =<< A
lem x A = P.⊆-antisym _ _
  (λ zs → rec squash₁ λ { 
    (_⊎_.inl r) → ∣ _⊎_.inl r ∣₁ ; 
    (_⊎_.inr m) → rec squash₁ (λ { (ys , yA , e) → ∣ _⊎_.inr ∣ ys , (yA , ∣ _⊎_.inr e ∣₁) ∣₁ ∣₁ }) m })
  (λ zs → rec squash₁ λ { 
    (_⊎_.inl r) → ∣ _⊎_.inl r ∣₁ ; 
    (_⊎_.inr p) → rec squash₁ (λ { (ys , yA , ysP) → rec squash₁ (λ { 
      (_⊎_.inl e) → ∣ _⊎_.inl ∣ _⊎_.inl e ∣₁ ∣₁ ; 
      (_⊎_.inr e) → ∣ _⊎_.inr ∣ ys , yA , e ∣₁ ∣₁ }) ysP }) p })


prefix-is-foldrM : prefix {X = X} ≡ foldrM pre (return [])
prefix-is-foldrM = foldrM-fixed-point-properties-eq⇐ pre (return []) prefix (refl , p)
  where
    p : (x : X) (xs : List X) → return [] ∪ (_∷_ x) <$> prefix xs ≡ pre x =<< prefix xs
    p x xs = P.⊆-antisym _ _
      (λ zs → rec squash₁ λ {
        (_⊎_.inl zs≡[]) → ∣ [] , nil∈prefix xs , ∣ _⊎_.inl zs≡[] ∣₁ ∣₁ ;
        (_⊎_.inr m) → rec squash₁ (λ { (ys , ys∈pfx , eq) → ∣ ys , ys∈pfx , ∣ _⊎_.inr eq ∣₁ ∣₁ }) m 
      })
      (λ zs → rec squash₁ λ {
        (ys , ys∈pfx , zs∈prexys) → rec squash₁ (λ {
          (_⊎_.inl zs≡[]) → ∣ _⊎_.inl zs≡[] ∣₁ ;
          (_⊎_.inr zs≡x∷ys) → ∣ _⊎_.inr ∣ ys , ys∈pfx , zs≡x∷ys ∣₁ ∣₁
        }) zs∈prexys
      })

lem1 : const (return []) ⊔ prefix+ {X = X} ≡ prefix
lem1 = 
  (const (return []) ⊔ prefix+)
  ≡⟨ foldrM-fixed-point-properties-eq⇐ pre (return []) (const (return []) ⊔ prefix+) (p1 , p2) ⟩ 
  foldrM pre (return [])
  ≡⟨ sym prefix-is-foldrM ⟩ 
  prefix
  ∎
  where
    p1 : (const (return []) ⊔ prefix+ {X = X}) [] ≡ return []
    p1 = 
      (const (return []) ⊔ prefix+) []
      ≡⟨ refl ⟩
      return [] ∪ ∅
      ≡⟨ return-∪-∅ [] ⟩
      return []
      ∎ 
    p2 : (x : X) (xs : List X) →
      (const (return []) ⊔ prefix+) (x ∷ xs) ≡
      (pre x =<< (const (return []) ⊔ prefix+) xs)
      
    p2 x xs = 
      return [] ∪ (prefix+ (x ∷ xs))
      ≡⟨ refl ⟩
      return [] ∪ (return [ x ] ∪ (_∷_ x) <$> (prefix+ xs))
      ≡⟨ sym (∪-assoc (return []) (return [ x ]) (_∷_ x <$> prefix+ xs)) ⟩ 
      return [] ∪ return [ x ] ∪ (_∷_ x) <$> (prefix+ xs)
      ≡⟨ lem x (prefix+ xs) ⟩ 
      return [] ∪ return [ x ] ∪ pre x =<< prefix+ xs
      ≡⟨ sym (cong (λ w → w ∪ pre x =<< prefix+ xs) (ret-left-id [] (pre x))) ⟩ 
      pre x =<< return [] ∪ pre x =<< prefix+ xs
      ≡⟨ sym (=<<-∪-dist-left (pre x) (return []) (prefix+ xs)) ⟩
      (pre x =<< (return [] ∪ prefix+ xs))
      ∎


-- Examples 1 prefix+ ⊆ prefix, prove by induction
example-1 : prefix+ {X = X} ⊑ prefix
example-1 [] zs zs∈∅ = elim* zs∈∅
example-1 (x ∷ xs) zs zs∈ = rec squash₁ helper zs∈
  where
    helper : (zs ∈ return [ x ]) ⊎ (zs ∈ ((_∷_ x) <$> prefix+ xs)) → zs ∈ prefix (x ∷ xs)
    helper (_⊎_.inl zs∈ret) = 
      ∣ _⊎_.inr ∣ [] , nil∈prefix xs , zs∈ret ∣₁ ∣₁
    helper (_⊎_.inr zs∈map) = 
      rec squash₁ 
        (λ { (ys , ys∈pfx+ , zs∈ret) → ∣ _⊎_.inr ∣ ys , example-1 xs ys ys∈pfx+ , zs∈ret ∣₁ ∣₁ }) 
        zs∈map


-- Empty list is always in pre
nil∈pre : ∀ {ℓ} {X : Type ℓ} → ∀ x ys → [] ∈ pre {X = X} x ys
nil∈pre x ys = ∣ _⊎_.inl ∣ refl ∣₁ ∣₁