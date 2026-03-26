{-# OPTIONS --cubical #-}
module Fold where

open import Data.List hiding (foldr)
open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Cubical.Data.Sigma.Base using (_×_) 

open import Monad_v2
  
private
    variable
        ℓ : Level
        A B C : Type ℓ 

foldrM : (A → B → ℙ B) → ℙ B → List A → ℙ B
foldrM f e []       = e 
foldrM f e (x ∷ xs) = f x =<< foldrM f e xs

foldr : (A → B → B) → B → List A → B
foldr f e []       = e 
foldr f e (x ∷ xs) = f x (foldr f e xs)

foldrM-fixed-point-properties-⇐ :
  (f : A → B → ℙ B)
  → (e : ℙ B)
  → (h : List A → ℙ B)
  → (base : e ⊆ h [])
  → (step : ∀ x xs → (f x =<< h xs) ⊆ h (x ∷ xs))
  → foldrM f e ⊑ h
foldrM-fixed-point-properties-⇐ f e h base step [] b b∈fold = base b b∈fold
foldrM-fixed-point-properties-⇐ f e h base step (x ∷ xs) b b∈fold = 
    let 
        -- goal b ∈ h (x ∷ xs)
        -- 1. b ∈ (f x =<< h xs)
        -- 2. step x xs b : b ∈ (f x =<< h xs) → b ∈ h (x ∷ xs)
        lem : b ∈ (f x =<< h xs)
        lem = rec squash₁ (λ {(b' , (b'∈fold , b∈fxb') ) → ∣ b' , foldrM-fixed-point-properties-⇐ f e h base step xs b' b'∈fold , b∈fxb' ∣₁ }) b∈fold
    in step x xs b lem

foldrM-fixed-point-properties-⇒ :
  (f : A → B → ℙ B)
  → (e : ℙ B)
  → (h : List A → ℙ B)
  → (base : h [] ⊆ e)
  → (step : ∀ x xs → h (x ∷ xs) ⊆ (f x =<< h xs))
  → h ⊑ foldrM f e
foldrM-fixed-point-properties-⇒ f e h base step [] b b∈h[] = base b b∈h[]
foldrM-fixed-point-properties-⇒ f e h base step (x ∷ xs) b b∈hxss = 
    let 
        ind : (f x =<< h xs) ⊆ (f x =<< foldrM f e xs) 
        ind = =<<-monotonic-right (f x) (h xs) (foldrM f e xs) (foldrM-fixed-point-properties-⇒  f e h base step xs)
        trans = P.⊆-trans (h (x ∷ xs)) (f x =<< h xs) (f x =<< foldrM f e xs) (step x xs) ind
    in trans b b∈hxss

foldrM-fixed-point-properties-eq : 
  (f : A → B → ℙ B)
  → (e : ℙ B)
  → (h : List A → ℙ B)
  → (h ≡ foldrM f e) → (h [] ≡ e) × (∀ x → ∀ xs →  (h (x ∷ xs)) ≡ f x =<< h xs )
foldrM-fixed-point-properties-eq f e h eq = (p1 , p2)
    where
        p1 : h [] ≡ e
        p1 = λ i → eq i []

        p2 : ∀ x xs → h (x ∷ xs) ≡ f x =<< h xs
        p2 x xs = (λ i → eq i (x ∷ xs)) ∙ (λ i → f x =<< eq (~ i) xs)

foldrM-fusion :
    (g : A → B → ℙ B)
    → (f : A → B → ℙ B)
    → (e : ℙ B)
    → (h : ℙ B → ℙ B) 
    → (p : ∀ x m → (g x =<< h m) ⊆ h (f x =<< m))
    →  foldrM g (h e) ⊑ h ∘ foldrM f e
foldrM-fusion g f e h p [] b q = q
foldrM-fusion g f e h p (y ∷ ys) b q = 
    let
        ind : (g y =<< foldrM g (h e) ys) ⊆ (g y =<< (h ∘ foldrM f e) ys)
        ind = =<<-monotonic-right (g y) (foldrM g (h e) ys) ((h ∘ foldrM f e) ys) (foldrM-fusion g f e h p ys) 

        trans = P.⊆-trans (g y =<< foldrM g (h e) ys) (g y =<< (h ∘ foldrM f e) ys) (h (foldrM f e (y ∷ ys)))
                ind (p y (foldrM f e ys)) b q
    in trans
        
    
foldrM-monotonic :
    (f₀ : A → B → ℙ B)
    → (f₁ : A → B → ℙ B)
    → (e₀ : ℙ B)
    → (e₁ : ℙ B)
    → (f₀⊑f₁ : ∀ x → f₀ x ⊑ f₁ x)
    → e₀ ⊆ e₁
    → foldrM f₀ e₀ ⊑ foldrM f₁ e₁
foldrM-monotonic f₀ f₁ e₀ e₁ f₀⊑f₁ e₀⊆e₁ [] = e₀⊆e₁
foldrM-monotonic f₀ f₁ e₀ e₁ f₀⊑f₁ e₀⊆e₁ (x ∷ xs) = 
    foldrM-fixed-point-properties-⇐ 
        f₀ e₀ (foldrM f₁ e₁) e₀⊆e₁ 
        (λ x' xs' → =<<-monotonic-left (foldrM f₁ e₁ xs') (f₀ x') (f₁ x') (f₀⊑f₁ x')) 
        (x ∷ xs)



foldrM-pure :
  (f : A → B → B)
  → (e : B)
  → (return ∘ (foldr f e)) ≡ foldrM (λ x → return ∘ f x) (return e)
foldrM-pure f e = funExt (λ x → help x) 
    where
        help : ∀ x → (return ∘ (foldr f e)) x ≡ foldrM (λ x → return ∘ f x) (return e) x
        help []       = refl
        help (x ∷ xs) = 
            return (f x (foldr f e xs))
                ≡⟨ refl ⟩
            (return ∘ f x) (foldr f e xs)
                ≡⟨ sym (ret-left-id (foldr f e xs) (return ∘ f x)) ⟩
            (return ∘ f x) =<< (return ∘ (foldr f e)) xs
                ≡⟨ cong (λ u → (return ∘ f x) =<< u) (help xs) ⟩
            (return ∘ f x) =<< foldrM (λ x → return ∘ f x) (return e) (xs)
                ≡⟨ refl ⟩
            foldrM (λ x → return ∘ f x) (return e) (x ∷ xs)
                ∎