{-# OPTIONS --cubical #-}
module HasMin where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation as PT hiding (map)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)
open import Cubical.Data.Sigma.Base using (_×_; Σ)
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)

open import Sets
open import Monad_v2
open import Min

module HasMinProps {ℓ : Level} {Y : Type ℓ} (R : Y → ℙ Y) 
    (minR-inst : MinR R)
    (R-refl  : ∀ x → x ∈ R x)
    (R-trans : ∀ x y z → x ∈ R y → y ∈ R z → x ∈ R z)
    (R-total : ∀ x y → ∥ (x ∈ R y) ⊎ (y ∈ R x) ∥₁) where

    open MinR minR-inst

    -- 1. The minimum of a singleton set `return y` is just `y`
    hasmin-return : ∀ (y : Y) → ∥ Σ Y (λ y' → y' ∈ minR (return y)) ∥₁
    hasmin-return y = ∣ y , (minR-property-⇐ (return y) y (y∈[y] y) (λ x x∈[y] → 
        rec (P.∈-isProp (R x) y) 
            (λ y≡x → subst (λ v → fst (R v y)) y≡x (R-refl y)) x∈[y])) ∣₁ 

    -- 2. If A and B have minimums, their union A ∪ B also has a minimum
    hasmin-union : (A B : ℙ Y) 
        → ∥ Σ Y (λ y → y ∈ minR A) ∥₁ 
        → ∥ Σ Y (λ y → y ∈ minR B) ∥₁ 
        → ∥ Σ Y (λ y → y ∈ minR (A ∪ B)) ∥₁
    hasmin-union A B minA minB = 
        rec squash₁ (λ { (mA , mA∈minA) → 
        rec squash₁ (λ { (mB , mB∈minB) → 
            
            -- Compare the minimum of A and the minimum of B
            let 
                case1 : mA ∈ R mB → ∥ Σ Y (λ y → y ∈ minR (A ∪ B)) ∥₁
                case1 mAmB = ∣ mA , minR-property-⇐ (A ∪ B) mA ∣ inl (minR-contained A mA mA∈minA) ∣₁ (λ x x∈A∪B → 
                    rec (P.∈-isProp (R x) mA) 
                        (λ { (inl x∈A) → minR-minimum A mA mA∈minA x x∈A 
                           ; (inr x∈B) → R-trans mA mB x mAmB (minR-minimum B mB mB∈minB x x∈B) 
                           }) 
                        x∈A∪B) ∣₁
                case2 : mB ∈ R mA → ∥ Σ Y (λ y → y ∈ minR (A ∪ B)) ∥₁
                case2 mBmA = ∣ mB , minR-property-⇐ (A ∪ B) mB ∣ inr (minR-contained B mB mB∈minB) ∣₁ (λ x x∈A∪B → 
                    rec (P.∈-isProp (R x) mB) 
                        (λ { (inl x∈A) → R-trans mB mA x mBmA (minR-minimum A mA mA∈minA x x∈A) 
                           ; (inr x∈B) → minR-minimum B mB mB∈minB x x∈B 
                           }) 
                        x∈A∪B) ∣₁
                
            in rec squash₁ (λ { (inl p) → case1 p ; (inr p) → case2 p }) (R-total mA mB)
                
        }) minB 
        }) minA
    
    is-mono : (Y → Y) → Type ℓ
    is-mono f = ∀ x y → x ∈ R y → f x ∈ R (f y)

    -- 3. If A has a minimum and f is monotonic, f <$> A has a minimum
    hasmin-fmap : (A : ℙ Y) (f : Y → Y) 
        → is-mono f 
        → ∥ Σ Y (λ y → y ∈ minR A) ∥₁ 
        → ∥ Σ Y (λ y → y ∈ minR (f <$> A)) ∥₁
    hasmin-fmap A f f-mono minA = 
        rec squash₁ (λ { (mA , mA∈minA) → 
            
            let 
                -- 1. Extract the proof that mA is actually in A
                mA∈A : mA ∈ A
                mA∈A = minR-contained A mA mA∈minA
                
                -- 2. Show f mA is in the mapped set (f <$> A)
                fmA∈fA : f mA ∈ (f <$> A)
                fmA∈fA = ∣ mA , mA∈A , y∈[y] (f mA) ∣₁ 
                
                -- 3. Show f mA is a lower bound for all y in f <$> A
                is-lower-bound : ∀ y → y ∈ (f <$> A) → f mA ∈ R y
                is-lower-bound y y∈fA = 
                    -- Unpack the existential y = f x for some x ∈ A
                    rec (P.∈-isProp (R y) (f mA)) 
                        (λ { (x , x∈A , y∈[fx]) → 
                            
                            -- Since mA is the minimum of A, mA <= x
                            let mA≤x : mA ∈ R x
                                mA≤x = minR-minimum A mA mA∈minA x x∈A
                                
                                -- Because f is monotonic, f mA <= f x
                                fmA≤fx : f mA ∈ R (f x)
                                fmA≤fx = f-mono mA x mA≤x
                                
                            -- Substitute f x ≡ y to conclude f mA <= y
                            in rec (P.∈-isProp (R y) (f mA)) (λ fx≡y  → subst (λ v → f mA ∈ R v) fx≡y fmA≤fx) y∈[fx]
                            
                        }) y∈fA

            -- 4. Package everything using minR-property-⇐
            in ∣ f mA , minR-property-⇐ (f <$> A) (f mA) fmA∈fA is-lower-bound ∣₁
            
        }) minA