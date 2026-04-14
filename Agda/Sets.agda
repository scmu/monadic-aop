{-# OPTIONS --cubical #-}
module Sets where

open import Cubical.Foundations.Prelude 
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma.Base using (_×_) 
open import Cubical.Functions.Logic
open import Cubical.HITs.PropositionalTruncation as PT hiding (map)
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Cubical.Data.Sum.Base using (_⊎_)    

private
  variable
    ℓ : Level
    X : Type ℓ

{-
Defined in Cubical.Foundations.Powerset.

ℙ : Type ℓ → Type (ℓ-suc ℓ)
ℙ X = X → hProp _ 
    = X → Σ[ Y ∈ Type _] (isProp Y)
    = X → Σ[ Y ∈ Type _] ((y₀ y₁ : Y) → y₀ ≡ y₁)
-}


∪-op : ℙ X → ℙ X → ℙ X
∪-op A B x = ∥ (x ∈ A) ⊎ (x ∈ B) ∥₁ , squash₁ -- (x ∈ A ⊎ x ∈ B) ≡  ⟨ A x ⟩ ⊎ ⟨ B x ⟩

infixl 6 _∪_

_∪_ : ℙ X → ℙ X → ℙ X
_∪_ = ∪-op


-- Union is commutative
∪-comm : (A B : ℙ X) → A ∪ B ≡ B ∪ A
∪-comm A B = P.⊆-extensionality (A ∪ B) (B ∪ A) ((λ x x₁ → rec (snd ((B ∪ A) x)) (helper x A B) x₁) , λ x x₁ → rec (snd ((A ∪ B) x)) (helper x B A) x₁)
    where
        helper : (x : X) → (A B : ℙ X) → (x ∈ A) ⊎ (x ∈ B) → (B ∪ A) x .fst
        helper x A B (_⊎_.inl x₁) = ∣ _⊎_.inr x₁ ∣₁
        helper x A B (_⊎_.inr x₁) = ∣ _⊎_.inl x₁ ∣₁

-- Union is associative
∪-assoc : (A B C : ℙ X) → (A ∪ B) ∪ C ≡ A ∪ (B ∪ C)
∪-assoc A B C = P.⊆-extensionality (A ∪ B ∪ C) (A ∪ (B ∪ C)) ((λ x x₁ → rec (snd ((A ∪ (B ∪ C)) x)) (helper x A B C) x₁) , λ x x₁ → rec (snd ((A ∪ B ∪ C) x)) (helper3 x A B C) x₁)
    where
        helper : (x : X) → (A B C : ℙ X) → (x ∈ A ∪ B) ⊎ (x ∈ C) → (A ∪ (B ∪ C)) x .fst
        helper x A B C (_⊎_.inl x₁) = rec (snd ((A ∪ (B ∪ C)) x)) helper2 x₁
            where
                helper2 : (x ∈ A) ⊎ (x ∈ B) → (A ∪ (B ∪ C)) x .fst
                helper2 (_⊎_.inl x) = ∣ _⊎_.inl x ∣₁
                helper2 (_⊎_.inr x) = ∣ _⊎_.inr ∣ _⊎_.inl x ∣₁ ∣₁
        helper x A B C (_⊎_.inr x₁) = ∣ _⊎_.inr ∣ _⊎_.inr x₁ ∣₁ ∣₁

        helper3 : (x : X) → (A B C : ℙ X) → (x ∈ A) ⊎ (x ∈ B ∪ C) → (A ∪ B ∪ C) x .fst
        helper3 x A B C (_⊎_.inl x₁) = ∣ _⊎_.inl ∣ _⊎_.inl x₁ ∣₁ ∣₁
        helper3 x A B C (_⊎_.inr x₁) = rec (snd ((A ∪ B ∪ C) x)) helper4 x₁
            where
                helper4 : (x ∈ B) ⊎ (x ∈ C) → (A ∪ B ∪ C) x .fst
                helper4 (_⊎_.inl x) = ∣ _⊎_.inl ∣ _⊎_.inr x ∣₁ ∣₁
                helper4 (_⊎_.inr x) = ∣ _⊎_.inr x ∣₁

-- Subset properties for union
⊆-∪-left : (A B : ℙ X) → A ⊆ (A ∪ B)
⊆-∪-left A B x = inl

⊆-∪-right : (A B : ℙ X) → B ⊆ (A ∪ B)
⊆-∪-right A B x = inr



-- intersection

_∩_ : ℙ X → ℙ X → ℙ X
_∩_ A B x = ((x ∈ A) × (x ∈ B)) , isProp× (P.∈-isProp A x) (P.∈-isProp B x)

-- ∈-∩ : {X : Set} →  (x : X) → (A B : ℙ X) → x ∈ (A ∩ B) ≃ (x ∈ A × x ∈ B)
-- ∈-∩ = ?

∩-comm : (A B : ℙ X) → A ∩ B ≡ B ∩ A
∩-comm A B = P.⊆-extensionality (A ∩ B) (B ∩ A) ((λ x z → z .snd , z .fst) , (λ x z → z .snd , z .fst))

∩-assoc : (A B C : ℙ X) → (A ∩ B) ∩ C ≡ A ∩ (B ∩ C)
∩-assoc A B C = P.⊆-extensionality ((A ∩ B) ∩ C) (A ∩ (B ∩ C)) ((λ x z → z .fst .fst , (z .fst .snd , z .snd)) , (λ x z → (z .fst , z .snd .fst) , z .snd .snd))

∩-∪-dist-r : (A B C : ℙ X) → (A ∩ (B ∪ C)) ⊆ ((A ∩ B) ∪ (A ∩ C))
∩-∪-dist-r A B C = λ x x₁ → rec squash₁ (((λ {(_⊎_.inl x∈A) → ∣ _⊎_.inl (x₁ .fst , x∈A) ∣₁ ; (_⊎_.inr x∈C) → ∣ _⊎_.inr (x₁ .fst , x∈C) ∣₁ }))) (x₁ .snd)

∩-∪-dist-l : (A B C : ℙ X) → ((A ∩ B) ∪ (A ∩ C)) ⊆ (A ∩ (B ∪ C))
∩-∪-dist-l A B C = λ x x₁ → rec (P.∈-isProp (A ∩ (B ∪ C)) x) (λ { (_⊎_.inl x∈ab) → x∈ab .fst , ∣ _⊎_.inl (x∈ab .snd) ∣₁ ; (_⊎_.inr x∈ac) → x∈ac .fst , ∣ _⊎_.inr (x∈ac .snd) ∣₁}) x₁

∩-∪-dist : (A B C : ℙ X) → A ∩ (B ∪ C) ≡ (A ∩ B) ∪ (A ∩ C)
∩-∪-dist A B C = P.⊆-extensionality (A ∩ (B ∪ C)) ((A ∩ B) ∪ (A ∩ C)) (∩-∪-dist-r A B C , ∩-∪-dist-l A B C)

-- todo
-- ∪-∩-dist :(A B C : ℙ X) → A ∪ (B ∩ C) ≡ (A ∪ B) ∩ (A ∪ C)
-- ∪-∩-dist A B C = P.⊆-extensionality (A ∪ (B ∩ C)) ((A ∪ B) ∩ (A ∪ C)) ({!   !} , {!   !})


⊆-∩-left : (A B : ℙ X) → (A ∩ B) ⊆ A
⊆-∩-left A B = λ x z → z .fst

⊆-∩-right : (A B : ℙ X) → (A ∩ B) ⊆ B
⊆-∩-right A B = λ x z → z .snd

-- ∪ and ⊆ 
⊆-∪-monotonic-left : (A B C : ℙ X) → A ⊆ B → (A ∪ C) ⊆ (B ∪ C)
⊆-∪-monotonic-left A B C A⊆B = λ x x∈A∪C → rec squash₁ 
    (λ { 
        (_⊎_.inl x∈A) → ∣ _⊎_.inl (A⊆B x x∈A) ∣₁ ; 
        (_⊎_.inr x∈C) → ∣ _⊎_.inr x∈C ∣₁ }
    )
    x∈A∪C

⊆-∪-monotonic-right : (A B C : ℙ X) → A ⊆ B → (C ∪ A) ⊆ (C ∪ B)
⊆-∪-monotonic-right A B C A⊆B = λ x x∈C∪A → rec squash₁ 
    (λ { 
        (_⊎_.inl x∈C) → ∣ _⊎_.inl x∈C ∣₁ ; 
        (_⊎_.inr x∈C) → ∣ _⊎_.inr (A⊆B x x∈C) ∣₁
    }) 
    x∈C∪A

∪-⊆-both : (A B C : ℙ X) → A ⊆ C → B ⊆ C → (A ∪ B) ⊆ C
∪-⊆-both A B C A⊆C B⊆C x x∈A∪B = 
  rec (P.∈-isProp C x) 
      (λ { (_⊎_.inl x∈A) → A⊆C x x∈A ; (_⊎_.inr x∈B) → B⊆C x x∈B }) 
      x∈A∪B

⊆-to-∪-≡ : (A B : ℙ X) → A ⊆ B → A ∪ B ≡ B
⊆-to-∪-≡ A B A⊆B = P.⊆-antisym (A ∪ B) B lhs rhs
  where
    lhs : (A ∪ B) ⊆ B
    lhs = ∪-⊆-both A B B A⊆B (λ _ x∈B → x∈B)
    
    rhs : B ⊆ (A ∪ B)
    rhs = ⊆-∪-right A B

∪-≡-to-⊆ : (A B : ℙ X) → A ∪ B ≡ B → A ⊆ B
∪-≡-to-⊆ A B eq x x∈A = 
  let x∈A∪B : x ∈ A ∪ B
      x∈A∪B = ⊆-∪-left A B x x∈A
  in subst (λ S → x ∈ S) eq x∈A∪B