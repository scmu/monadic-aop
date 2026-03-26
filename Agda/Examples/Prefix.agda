{-# OPTIONS --cubical #-}
module Examples.Prefix where
    
open import Data.List hiding (foldr; head)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Cubical.Data.Sigma.Base using (_×_) 
open import Cubical.Functions.Logic
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

∅ : ℙ X
∅ x = ⊥* , isProp⊥*

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


lem1 : ∀ xs → return [] ∪ prefix+ {X = X} xs ≡ prefix xs
lem1 [] = {!   !}
lem1 (x ∷ xs) = let
  
  p1 : return [ x ] ∪ (_∷_ x <$> prefix+ xs) ≡ (pre x =<< prefix+ xs)
  p1 = snd (foldrM-fixed-point-properties-eq pre (return []) (prefix+) {!   !}) x xs

-- goal : return [] ∪ (return [ x ] ∪ (_∷_ x <$> prefix+ xs)) ≡ return [] ∪ (_∷_ x <$> prefix xs)
-- apply p1:  return [] ∪ (pre x =<< prefix+ xs) ≡ return [] ∪ (_∷_ x <$> prefix xs)
-- we need idempotentency of ∪,
-- then we need (pre x =<< prefix+ xs) ≡ (_∷_ x <$> prefix xs)



  in {! foldrM-fixed-point-properties-eq  !}
 
-- snd(foldrM-fixed-point-properties-eq pre (return []) (prefix) ?) x xs
-- return [] ∪ (_∷_ x <$> prefix xs) ≡ (pre x =<< prefix xs)


  -- a = {!  (snd (foldrM-fixed-point-properties-eq pre (return []) (prefix') ?) ? ?)   !}
 
  -- in {!   !}





-- Empty list is always a prefix
nil∈prefix : ∀ {ℓ} {X : Type ℓ} → ∀ xs → [] ∈ prefix {X = X} xs
nil∈prefix [] = ∣ refl ∣₁
nil∈prefix (x ∷ xs) = ∣ _⊎_.inl ∣ refl ∣₁ ∣₁


-- Examples 1 prefix+ ⊆ prefix
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

-- ∀ xs → xs ∈ prefix+ xs
head∈prefix+ : ∀ {ℓ} {X : Type ℓ} → ∀ (xs : List X) → xs ∈ prefix+ xs
head∈prefix+ [] = {!   !} 
head∈prefix+ (x ∷ xs) = ∣ _⊎_.inr ∣ xs , (head∈prefix+ xs , ∣ refl ∣₁) ∣₁ ∣₁

-- prefix can be defined with foldrM
-- prefix_foldrM : ∀ {ℓ} {X : Type ℓ} → ∀ xs → foldrM {X = ?} pre (return []) xs ≡ prefix xs
-- prefix_foldrM [] = funExt λ x → refl
-- prefix_foldrM (x ∷ xs) = 
--   foldrM pre (return []) (x ∷ xs)
--     ≡⟨ refl ⟩
--   (pre x =<< foldrM pre (return []) xs)
--     ≡⟨ cong (pre x =<<_) (prefix_foldrM xs) ⟩
--   (pre x =<< prefix xs)
--     ≡⟨ lemma x xs ⟩
--   prefix (x ∷ xs)
--     ∎
--   where
--     lemma : ∀ x xs → (pre x =<< prefix xs) ≡ prefix (x ∷ xs)
--     lemma x xs = funExt λ zs → ⇔toPath (fwd x xs zs) (bwd x xs zs)
--       where
--         fwd : ∀ x xs zs → zs ∈ (pre x =<< prefix xs) → zs ∈ prefix (x ∷ xs)
--         fwd x xs zs zs∈lhs = rec squash₁ helper zs∈lhs
--           where
--             helper : Σ _ (λ ys → (ys ∈ prefix xs) × (zs ∈ pre x ys)) → zs ∈ prefix (x ∷ xs)
--             helper (ys , ys∈pfx , zs∈prexys) = rec squash₁ helper2 zs∈prexys
--               where
--                 helper2 : (zs ∈ return []) ⊎ (zs ∈ return (x ∷ ys)) → zs ∈ prefix (x ∷ xs)
--                 helper2 (_⊎_.inl zs≡[]) = ∣ _⊎_.inl zs≡[] ∣₁
--                 helper2 (_⊎_.inr zs≡x∷ys) = ∣ _⊎_.inr ∣ ys , ys∈pfx , zs≡x∷ys ∣₁ ∣₁
        
--         bwd : ∀ x xs zs → zs ∈ prefix (x ∷ xs) → zs ∈ (pre x =<< prefix xs)
--         bwd x xs zs zs∈rhs = rec squash₁ helper zs∈rhs
--           where            
--             helper : (zs ∈ return []) ⊎ (zs ∈ ((_∷_ x) <$> prefix xs)) → zs ∈ (pre x =<< prefix xs)
--             helper (_⊎_.inl zs≡[]) = rec squash₁ (λ eq → ∣ ([] , (nil∈prefix xs , rec squash₁ (λ eq → ∣ _⊎_.inl zs≡[] ∣₁) zs≡[])) ∣₁) zs≡[]
--             helper (_⊎_.inr zs∈map) = 
--               rec squash₁ 
--                 (λ { (ys , ys∈pfx , x∷ys≡zs) → ∣ ys , ys∈pfx , ∣ _⊎_.inr x∷ys≡zs ∣₁ ∣₁ }) 
--                 zs∈map


-- prefix+ can be defined with foldrM

-- prefix+_foldrM : ∀ {ℓ} {X : Type ℓ} → ∀ xs → foldrM {X = X} pre+ ∅ xs ≡ prefix+ xs
-- prefix+_foldrM [] = refl
-- prefix+_foldrM (x ∷ []) = funExt λ zs → ⇔toPath (fwd x zs) (bwd x zs)
--   where
--     fwd : ∀ x zs → zs ∈ (pre+ x =<< ∅) → zs ∈ prefix+ (x ∷ [])
--     fwd x zs zs∈lhs = rec squash₁ (λ { (ys , ys∈∅ , _) → elim* ys∈∅ }) zs∈lhs
    
--     bwd : ∀ x zs → zs ∈ prefix+ (x ∷ []) → zs ∈ (pre+ x =<< ∅)
--     bwd x zs zs∈rhs = rec squash₁ helper zs∈rhs
--       where
--         helper : (zs ∈ return [ x ]) ⊎ (zs ∈ ((_∷_ x) <$> ∅)) → zs ∈ (pre+ x =<< ∅)
--         helper (_⊎_.inl zs≡[x]) = {!   !}
--         helper (_⊎_.inr zs∈map) = rec squash₁ (λ { (ys , ys∈∅ , _) → elim* ys∈∅ }) zs∈map 
  -- foldrM pre+ ∅ (x ∷ xs)
  --   ≡⟨ refl ⟩
  -- (pre+ x =<< foldrM pre+ ∅ xs)
  --   ≡⟨ cong (pre+ x =<<_) (prefix+_foldrM xs) ⟩
  -- (pre+ x =<< prefix+ xs)
  --   ≡⟨ lemma x xs ⟩
  -- prefix+ (x ∷ xs)
  --   ∎
  -- where
  --   lemma : ∀ x xs → (pre+ x =<< prefix+ xs) ≡ prefix+ (x ∷ xs)
  --   lemma x xs = funExt λ zs → ⇔toPath (fwd x xs zs) (bwd x xs zs)
  --     where
  --       fwd : ∀ x xs zs → zs ∈ (pre+ x =<< prefix+ xs) → zs ∈ prefix+ (x ∷ xs)
  --       fwd x xs zs zs∈lhs = rec squash₁ helper zs∈lhs
  --         where
  --           helper : Σ _ (λ ys → (ys ∈ prefix+ xs) × (zs ∈ pre+ x ys)) → zs ∈ prefix+ (x ∷ xs)
  --           helper (ys , ys∈pfx+ , zs∈prexys) = rec squash₁ helper2 zs∈prexys
  --             where
  --               helper2 : (zs ∈ return [ x ]) ⊎ (zs ∈ return (x ∷ ys)) → zs ∈ prefix+ (x ∷ xs)
  --               helper2 (_⊎_.inl zs≡[x]) = ∣ _⊎_.inl zs≡[x] ∣₁
  --               helper2 (_⊎_.inr zs≡x∷ys) = ∣ _⊎_.inr ∣ ys , ys∈pfx+ , zs≡x∷ys ∣₁ ∣₁
        
  --       bwd : ∀ x xs zs → zs ∈ prefix+ (x ∷ xs) → zs ∈ (pre+ x =<< prefix+ xs)
  --       bwd x xs zs zs∈rhs = rec squash₁ helper zs∈rhs
  --         where
  --           helper : (zs ∈ return [ x ]) ⊎ (zs ∈ ((_∷_ x) <$> prefix+ xs)) → zs ∈ (pre+ x =<< prefix+ xs)
  --           helper (_⊎_.inl y) = rec squash₁ (λ x₄ → ∣ [] , ({!   !} , ∣ _⊎_.inr ∣ x₄ ∣₁ ∣₁) ∣₁) y
  --           helper (_⊎_.inr x) = {!   !}
