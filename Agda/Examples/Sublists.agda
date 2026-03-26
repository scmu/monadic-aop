{-# OPTIONS --cubical #-}
module Examples.Sublists where

open import Cubical.Foundations.Powerset as P -- using (ℙ; _∈_; _⊆_; ⊆-refl)
open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Data.Sum.Base using (_⊎_)

open import Data.List
open import Sets
open import Monad_v2
open import Reasoning

private
  variable
    X : Type

sublists : List X → ℙ (List X) 
sublists []       = return []
sublists (x ∷ xs) = yss ∪ (_∷_ x) <$> yss
    where yss = sublists xs

  -- sublists having an even number of elements 

evnsublists : List X → ℙ (List X)
evnsublists []           = return []
evnsublists (x ∷ [])     = return []
evnsublists (x ∷ y ∷ xs) = yss ∪ (_∷_ x) <$> ((_∷_ y) <$> yss)
   where yss = evnsublists xs

sublists⊇[] : (xs : List X) → return [] ⊆ sublists xs  
sublists⊇[] [] _ x∈return[] = x∈return[]
sublists⊇[] (x ∷ xs) ys ys∈return[] = ∣ _⊎_.inl (sublists⊇[] xs ys ys∈return[]) ∣₁

-- sublists⊒evnsublists : ∀ {X} → sublists {X} ⊒ evnsublists {X}
-- sublists⊒evnsublists {X} [] = λ x z → z
-- sublists⊒evnsublists {X} (x ∷ []) = λ x₁ z → ∣ _⊎_.inl z ∣₁
-- sublists⊒evnsublists {X} (x ∷ y ∷ xs) = reasoning (
--   ⊆begin
--   evnsublists {X} (x ∷ (y ∷ xs))
--   ⊆⟨ ⊆'-refl ⟩ 
--   evnsublists {X} xs ∪ (_∷_ x) <$> ((_∷_ y) <$> evnsublists xs)
--   ⊆⟨ ⊆-∪-monotonic-left (evnsublists {X} xs) (sublists xs) ((_∷_ x) <$> ((_∷_ y) <$> evnsublists xs)) (incl (evnsublists xs) (sublists xs) (sublists⊒evnsublists xs)) ⟩ 
--   sublists xs ∪ (_∷_ x) <$> ((_∷_ y) <$> evnsublists xs)
--   ⊆⟨ ⊆-∪-monotonic-right (((_∷_ x) <$> ((_∷_ y) <$> evnsublists xs))) (((_∷_ x) <$> ((_∷_ y) <$> sublists xs))) (sublists xs) (<$>-monotonic (_∷_ x) (<$>-monotonic (_∷_ y) (incl (evnsublists xs) (sublists xs) (sublists⊒evnsublists xs)))) ⟩ 
--   sublists xs ∪ (_∷_ x) <$> ((_∷_ y) <$> sublists xs)
--   ⊆⟨ ⊆-∪-monotonic-right (_∷_ x <$> (_∷_ y <$> sublists xs))
--     (_∷_ x <$> (sublists xs ∪ (_∷_ y <$> sublists xs))) (sublists xs) (>>=-monotonic (λ ys → return (x ∷ ys))  (incl (((_∷_ y) <$> sublists xs)) (sublists xs ∪ (_∷_ y) <$> sublists xs) (λ x₁ z → ∣ _⊎_.inr z ∣₁))) ⟩ 
--   sublists xs ∪ (_∷_ x) <$> (sublists xs ∪ (_∷_ y) <$> sublists xs)
--   ⊆⟨ ⊆'-refl ⟩ 
--   sublists xs ∪ (_∷_ x) <$> (sublists (y ∷ xs))
--   ⊆⟨ ⊆-∪-monotonic-left (sublists xs) ((sublists xs ∪ (_∷_ y) <$> sublists xs)) ((_∷_ x) <$> (sublists (y ∷ xs))) (incl (sublists xs) (sublists xs ∪ (_∷_ y <$> sublists xs)) (λ x₁ z → ∣ _⊎_.inl z ∣₁)) ⟩ 
--   (sublists xs ∪ (_∷_ y) <$> sublists xs) ∪ (_∷_ x) <$> (sublists (y ∷ xs))
--   ⊆⟨ ⊆'-refl ⟩ 
--   sublists (y ∷ xs) ∪ (_∷_ x) <$> (sublists (y ∷ xs))
--   ⊆⟨ ⊆'-refl ⟩ 
--   sublists (x ∷ y ∷ xs)
--   ⊆∎
--   ) 



{- 
    evnsublists (x ∷ y ∷ xs) 
  =   {- definition of evnsublists -}
    evnsublists xs ∪ (_∷_ x) <$> ((_∷_ y) <$> evnsublists xs)
  ⊆   {- induction -} -- split to two steps
    sublists xs ∪ (_∷_ x) <$> ((_∷_ y) <$> sublists xs)
  ⊆   {- mononticity of (>>=) -}
    sublists xs ∪ (_∷_ x) <$> (sublists xs ∪ (_∷_ y) <$> sublists xs)
  =   {- definition of sublists -}
    sublists xs ∪ (_∷_ x) <$> (sublists (y ∷ xs)) 
  ⊆   {- mononticity of ∪ -} 
    (sublists xs ∪ (_∷_ y) <$> sublists xs) ∪ (_∷_ x) <$> (sublists (y ∷ xs)) 
  =   {- definition of sublists -}
    sublists (y ∷ xs) ∪ (_∷_ x) <$> (sublists (y ∷ xs)) 
  =   {- definition of sublists -}
    sublists (x ∷ y ∷ xs)
-}

   