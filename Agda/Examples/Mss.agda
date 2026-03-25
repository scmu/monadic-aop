{-# OPTIONS --cubical #-}
module Examples.Mss where

open import Data.List hiding (foldr; head)
open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Cubical.Data.Sigma.Base using (_×_) 
open import Cubical.Data.Sum.Base using (_⊎_) 
open import Cubical.Data.Int using (ℤ)
open import Cubical.Data.Empty

open import Monad_v2
open import Fold 
open import Sets 

prefix : ∀ {ℓ} {A : Type ℓ} → List A → ℙ (List A) 
prefix []       = return []
prefix (x ∷ xs) = return [] ∪ (_∷_ x) <$> (prefix xs)

pre : ∀ {ℓ} {A : Type ℓ} → A → List A → ℙ (List A) 
pre x ys = return [] ∪ return (x ∷ ys)

suffix : ∀ {ℓ} {A : Type ℓ} → List A → ℙ (List A) 
suffix [] = return []
suffix (x ∷ xs) = return (x ∷ xs) ∪ suffix xs

wrap : ∀ {ℓ} {A : Type ℓ} → A → List A
wrap x = [ x ]

-- returns e if the list is empty
head : ∀ {ℓ} {A : Type ℓ} → A → List A → A
head e [] = e
head e (x ∷ xs) = x

scanR : 
    ∀ {ℓ} {A B : Type ℓ} →
    (A → B → ℙ B) → ℙ B → List A → ℙ (List B)
scanR f e [] = wrap <$> e
scanR f e (x ∷ xs) = scanR f e xs >>= λ ys → f x (head _ ys) >>= λ z → return (z ∷ ys)


-- lems
a∈returna : ∀ {ℓ} {A : Type ℓ} → ∀ {a : A} → a ∈ return a
a∈returna = ∣ refl ∣₁ 


prefix2 : ∀ {ℓ} {A : Type ℓ} → ∀ xs → foldrM {A = A} pre (return []) xs ≡ prefix xs
prefix2 {ℓ} {A} [] = refl
prefix2 {ℓ} {A} (x ∷ xs) = {!   !}