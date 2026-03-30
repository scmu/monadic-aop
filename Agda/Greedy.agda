{-# OPTIONS --cubical #-}
module Greedy where
    
open import Data.List hiding (foldr; head)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Cubical.Data.Sigma.Base using (_×_) 
open import Cubical.Data.Sum.Base using (_⊎_) 
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Empty using (isProp⊥; isProp⊥* ; ⊥* ; elim*)

open import Monad_v2
open import Fold
open import Sets
open import Min

Hoare-Monotonic : ∀ {ℓ} {Y : Type ℓ} → (R : Y → ℙ Y) → (f : Y → ℙ Y) → Type ℓ
Hoare-Monotonic {Y = Y} R f = 
    ∀ y1 y0 z0 → y1 ∈ R y0 → z0 ∈ f y0 → 
    ∥ Σ Y (λ z1 → (z1 ∈ f y1) × (z1 ∈ R z0)) ∥₁

module _ {ℓ : Level} {Y : Type ℓ} (R : Y → ℙ Y) (M : MinR R) where
  
    -- Open the record here, bringing `minR`, `mf⊑f`, etc. into scope
    open MinR M
    greedy_thm-proved-by-induction : {X : Type ℓ} (f : X → Y → ℙ Y) 
        → (hoare : ∀ x → Hoare-Monotonic R (f x))
        → (trans : ∀ a b c → a ∈ R b → b ∈ R c → a ∈ R c) 
        → (e : ℙ Y) → 
        foldrM (λ x → minR ∘ f x) (minR e) ⊑ minR ∘ foldrM f e
    
    -- Base case: foldrM f e [] is e, so we just need minR e ⊆ minR e
    greedy_thm-proved-by-induction f hoare trans e [] y y∈ = y∈
    
    -- Inductive case
    greedy_thm-proved-by-induction f hoare trans e (x ∷ xs) y y∈ = 
        let 
        P_xs = foldrM (λ x' → minR ∘ f x') (minR e) xs
        Q_xs = foldrM f e xs
        
        -- IH : P_xs ⊆ minR (Q_xs)
        IH : P_xs ⊆ minR Q_xs
        IH = greedy_thm-proved-by-induction f hoare trans e xs

        -- ys is the left-hand side of the sequence, xs_full is the un-minimized right-hand side
        ys = (minR ∘ f x) =<< P_xs
        xs_full = f x =<< Q_xs

        -- condition 1: P_xs generated paths are subset of un-minimized Q_xs paths
        ys⊆xs_full : ys ⊆ xs_full
        ys⊆xs_full y1 y1-in = 
          rec squash₁ (λ { (b1 , b1-in-P , y1-in-min) → 
            let b1-in-Q = minR-id Q_xs b1 (IH b1 b1-in-P)
                y1-in-normal = minR-id (f x b1) y1 y1-in-min
            in ∣ b1 , b1-in-Q , y1-in-normal ∣₁ 
          }) y1-in

        -- condition 2: any y1 derived from LHS is better than any y0 derived from RHS
        c2 : ∀ y1 → y1 ∈ ys → ∀ y0 → y0 ∈ xs_full → y1 ∈ R y0
        c2 y1 y1-in y0 y0-in = 
          rec (P.∈-isProp (R y0) y1) (λ { (b1 , b1-in-P , y1-in-min) → 
            rec (P.∈-isProp (R y0) y1) (λ { (b0 , b0-in-Q , y0-in-normal) → 
              let
                 -- Get b1 ∈ R b0 using max-cancelation (minR-minimum) logic
                 b1-in-minQ = IH b1 b1-in-P
                 b1-R-b0 = minR-minimum Q_xs b1 b1-in-minQ b0 b0-in-Q
              in rec (P.∈-isProp (R y0) y1) (λ { (z1 , z1-in-f-b1 , z1-R-y0) → 
                 let y1-R-z1 = minR-minimum (f x b1) y1 y1-in-min z1 z1-in-f-b1
                 in trans y1 z1 y0 y1-R-z1 z1-R-y0
               }) (hoare x b1 b0 y0 b1-R-b0 y0-in-normal)
            }) y0-in
          }) y1-in
          
        -- applying the set-level universal property of minR
        in set-property-⇐ xs_full ys ys⊆xs_full c2 y y∈
    
    greedy_thm-proved-by-foldR-fusion : {X : Type ℓ} (f : X → Y → ℙ Y) 
        → (hoare : ∀ x → Hoare-Monotonic R (f x))
        → (trans : ∀ a b c → a ∈ R b → b ∈ R c → a ∈ R c) 
        → (e : ℙ Y) → 
        foldrM (λ x → minR ∘ f x) (minR e) ⊑ minR ∘ foldrM f e
    greedy_thm-proved-by-foldR-fusion {X} f hoare trans e = foldrM-fixed-point-properties-⇐ (λ x → minR ∘ f x) (minR e)
      (minR ∘ foldrM f e) (P.⊆-refl (minR e)) pf2
      where 
        pf2 : (x : X) → ((minR ∘ f x) <=< (minR ∘ foldrM f e)) ⊑ minR ∘ (f x <=< foldrM f e) 
        pf2 x = universal-property-⇐ ((minR ∘ f x) <=< (minR ∘ foldrM f e)) (f x <=< foldrM f e) (pf2-1 , pf2-2)
          where
            pf2-1 : ((minR ∘ f x) <=< (minR ∘ foldrM f e)) ⊑ (f x <=< foldrM f e)
            pf2-1 = ⊑-trans {r = (minR ∘ f x) <=< (minR ∘ foldrM f e)}
                            {s = f x <=< (minR ∘ foldrM f e)}
                            {t = f x <=< foldrM f e}
                            (<=<-monotonic-left (minR ∘ foldrM f e) (minR ∘ f x) (f x) (mf⊑f (f x)))
                            (<=<-monotonic-right (f x) (minR ∘ foldrM f e) (foldrM f e) (mf⊑f (foldrM f e)))
            pf2-2 : (((minR ∘ f x) <=< (minR ∘ foldrM f e)) <=< ((f x <=< foldrM f e) °)) ⊑ R
            pf2-2 = let

                -- Apply the min-cancellation law, the righthand side:
                step2 : 
                    ∀ y1 → ∀ y0 → ∀ b1 → ∀ b0 
                    → (b1-R-b0 : b1 ∈ R b0)       
                    → (l1 : y1 ∈ minR (f x b1))   
                    → (l3 : y0 ∈ f x b0)          
                    → y1 ∈ R y0
                step2 y1 y0 b1 b0 b1-R-b0 l1 l3 = 
                    rec (P.∈-isProp (R y0) y1) (λ { (z1 , z1-in-f-b1 , z1-R-y0) → 
                      let y1-R-z1 = minR-minimum (f x b1) y1 l1 z1 z1-in-f-b1
                      in trans y1 z1 y0 y1-R-z1 z1-R-y0
                    }) (hoare x b1 b0 y0 b1-R-b0 l3) 

                -- Expend the lefthand side
                step1 :
                    ∀ xs → ∀ y1 → ∀ y0 → ∀ b1 → ∀ b0 
                    → (l0 : b1 ∈ minR (foldrM f e xs)) 
                    → (l1 : y1 ∈ minR (f x b1)) 
                    → (l2 : b0 ∈ foldrM f e xs) 
                    → (l3 : y0 ∈ f x b0)
                    → y1 ∈ R y0
                step1 xs y1 y0 b1 b0 l0 l1 l2 l3 = 
                    let 
                       b1-R-b0 : b1 ∈ R b0
                       b1-R-b0 = minR-minimum (foldrM f e xs) b1 l0 b0 l2
                    in step2 y1 y0 b1 b0 b1-R-b0 l1 l3

                -- Rewrite in do-notation style
                step0 : 
                    ∀ xs → ∀ y1 → ∀ y0
                    → (l0 : y1 ∈ (minR ∘ f x) =<< (minR (foldrM f e xs))) 
                    → (l1 : y0 ∈ f x =<< foldrM f e xs)
                    → y1 ∈ R y0
                step0 xs y1 y0 l0 l1 = 
                    rec (P.∈-isProp (R y0) y1) 
                        (λ { (b1 , b1-in , y1-in) → 
                          rec (P.∈-isProp (R y0) y1) 
                              (λ { (b0 , b0-in , y0-in) → 
                                step1 xs y1 y0 b1 b0 b1-in y1-in b0-in y0-in 
                              }) 
                              l1 
                        }) 
                        l0

                in λ y0 y1 p → rec (P.∈-isProp (R y0) y1) (λ { (xs , y0-in , y1-in) → step0 xs y1 y0 y1-in y0-in }) p