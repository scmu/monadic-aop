{-# OPTIONS --cubical #-}
module Examples.Mss where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Cubical.Data.Sigma.Base using (_×_) 
open import Cubical.Data.Sum.Base using (_⊎_) 
open import Cubical.Data.Int
open import Cubical.Data.List hiding (rec)
open import Cubical.Data.Int.Order as Order using (_≤_; ≤Dec; isTrans≤; isRefl≤; ≤-o+-cancel)
open import Cubical.Relation.Nullary using (yes; no; Dec)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty using (isProp⊥; isProp⊥* ; ⊥* ; elim*; ⊥)

open import Monad_v2
open import Min
open import MonadicList 
open import Sets 
open import Reasoning 
open import HasMin 
open import Greedy 

sumℤ : List ℤ → ℤ
sumℤ [] = 0
sumℤ (x ∷ xs) = x + sumℤ xs

zplus : ℤ → List ℤ → List ℤ
zplus x ys with ≤Dec (x + sumℤ ys) 0
... | yes _ = []
... | no  _ = x ∷ ys

_≥ₛ_ : List ℤ → ℙ (List ℤ)
_≥ₛ_ xs = λ ys → ∥ sumℤ xs ≤ sumℤ ys ∥₁ , squash₁

Max≥ₛ : MinR _≥ₛ_
Max≥ₛ = record
  { minR = λ xs maxxs → 
      ((maxxs ∈ xs) × (∀ x → x ∈ xs → fst (_≥ₛ_ x maxxs))) , 
      isProp× (snd (xs maxxs)) (isPropΠ λ x → isPropΠ λ _ → squash₁)
      
  ; universal-property-⇒ = λ P f P⊑maxR∘f → 
      ( (λ x y y∈Px → fst (P⊑maxR∘f x y y∈Px))
      , (λ y y' y'∈P<=<f°y → 
          rec squash₁ 
              (λ { (x , y∈fx , y'∈Px) → snd (P⊑maxR∘f x y' y'∈Px) y y∈fx }) 
              y'∈P<=<f°y)
      )
      
  ; universal-property-⇐ = λ P f P⊑-h x y y∈Px → 
      let 
        (P⊑f , P<=<f°⊑R) = P⊑-h
        y∈fx = P⊑f x y y∈Px
        is-max = λ y' y'∈fx → P<=<f°⊑R y' y ∣ x , y'∈fx , y∈Px ∣₁
      in y∈fx , is-max
  }

open MinR Max≥ₛ

≥ₛ-refl : (x : List ℤ) → x ∈ _≥ₛ_ x
≥ₛ-refl x = ∣ 0 , refl ∣₁

≥ₛ-trans : ∀ x y z → x ∈ _≥ₛ_ y → y ∈ _≥ₛ_ z → x ∈ _≥ₛ_ z
≥ₛ-trans x y z x≥y y≥z = PT.map2 (λ x≥y' y≥z' → isTrans≤ y≥z' x≥y') x≥y y≥z 

≥ₛ-total : ∀ x y → ∥ (x ∈ _≥ₛ_ y) ⊎ (y ∈ _≥ₛ_ x) ∥₁
≥ₛ-total x y with (sumℤ x) Order.≟ (sumℤ y)
... | Order.lt x<y = ∣ _⊎_.inr ∣ Order.<-weaken x<y ∣₁ ∣₁
... | Order.eq x≡y = ∣ _⊎_.inr ∣ 0 , x≡y ∣₁ ∣₁
... | Order.gt y<x = ∣ _⊎_.inl ∣ Order.<-weaken y<x ∣₁ ∣₁

open HasMinProps _≥ₛ_ Max≥ₛ ≥ₛ-refl ≥ₛ-trans ≥ₛ-total


mss : List ℤ → ℙ (List ℤ)
mss = minR ∘ (prefix <=< suffix) 

maxPre : ℤ → List ℤ → ℙ (List ℤ)
maxPre x = minR ∘ pre x

minR-return-[] : minR (return []) ≡ return []
minR-return-[] = P.⊆-extensionality (minR (return [])) (return []) (minR-id (return []) , return-[]⊆minR)
    where
        return-[]⊆minR : return [] ⊆ minR (return [])
        return-[]⊆minR = set-property-⇐ (return []) (return []) (λ x z → z) λ y y∈[] y' y'∈[] → ≥ₛ-trans y [] y' 
            (rec squash₁ (λ []≡y → ∣ 0 , (λ i → sumℤ ([]≡y i)) ∣₁) y∈[]) 
            ((rec squash₁ (λ []≡y → ∣ 0 , (λ i → sumℤ (sym []≡y i)) ∣₁) y'∈[])) 

mss-thm : minR ∘ member ∘ scanr zplus [] ⊑ mss
mss-thm  = reasoning⊑ (
    ⊑begin
        
    (minR ∘ member ∘ scanr zplus []) 

    ≡⟨ {!   !} ⟩⊑
    minR ∘ (member <=< (return ∘ scanr zplus []))
    
    ≡⟨ {!   !} ⟩⊑
    minR ∘ (member <=< scanrM maxPre (return []))
    
    
    -- Scan Lemma -- member <=< scanrM maxPre e ⊑ foldrM maxPre e <=< suffix
    ⊑⟨ incl⊑ (minR-conditional-monotonicity-func (m <=< h) (f <=< s) (scan-lemma maxPre (return [])) lem-2 R-trans-≥ₛ) ⟩
    minR ∘ (foldrM maxPre (return []) <=< suffix)
    
    -- Greedy Theorem & Monotonicity
    ⊑⟨ incl⊑ (minR-conditional-monotonicity-func (f <=< s) (g <=< s) f<=<s⊑g<=<s lem-1 R-trans-≥ₛ) ⟩
    
    -- minR-<=<-Promotion
    minR ∘ ((minR ∘ prefix) <=< suffix)
    ≡⟨ sym (minR-<=<-Promotion prefix suffix hasmin-prefix R-trans-≥ₛ) ⟩⊑
    mss -- minR ∘ (prefix <=< suffix) 
    ⊑∎ 
    )
    where
        f = foldrM maxPre (return [])
        g = (minR ∘ prefix)
        s = suffix
        m = member
        h = scanrM maxPre (return [])

        -- minR-<=<-Promotion
        R-trans-≥ₛ : R-trans _≥ₛ_
        R-trans-≥ₛ x y z yRx zRy = ≥ₛ-trans z y x zRy yRx

        is-mono_∷_ : ∀ x → is-mono (_∷_ x) 
        is-mono_∷_ x y z y≥z = ∣ Order.≤-o+ {m = sumℤ z} {n = sumℤ y} {o = x} (rec Order.isProp≤ id y≥z) ∣₁ 

        hasmin-prefix : ∀ z → ∥ Σ (List ℤ) (λ y → y ∈ minR (prefix z)) ∥₁
        hasmin-prefix [] = hasmin-return []
        hasmin-prefix (x ∷ xs) = hasmin-union (return []) (_∷_ x <$> prefix xs) (hasmin-return []) (hasmin-fmap (prefix xs) (_∷_ x) (is-mono_∷_ x) (hasmin-prefix xs))    

        hasmin-pre : ∀ x ys → ∥ Σ (List ℤ) (λ y → y ∈ minR (pre x ys)) ∥₁
        hasmin-pre x ys = hasmin-union (return []) (return (x ∷ ys)) 
            (hasmin-return []) (hasmin-return (x ∷ ys))

        hasmin-foldrMx : ∀ z → ∥ Σ (List ℤ) (λ y → y ∈ foldrM maxPre (return []) z) ∥₁
        hasmin-foldrMx [] = ∣ [] , y∈[y] [] ∣₁
        hasmin-foldrMx (x ∷ xs) = 
            let 
                prev-hasmin = hasmin-foldrMx xs
            in rec squash₁ (λ { (ys , ys∈fold) → 
                rec squash₁ (λ { (y , y∈max) → ∣ y , ∣ ys , ys∈fold , y∈max ∣₁ ∣₁ }) (hasmin-pre x ys)
            }) prev-hasmin
        
        hasmin-f : ∀ z → ∥ Σ (List ℤ) (λ y → y ∈ prefix z) ∥₁ → ∥ Σ (List ℤ) (λ y → y ∈ foldrM maxPre (return []) z) ∥₁
        hasmin-f z _ = hasmin-foldrMx z

        -- Greedy Theorem
        
        hoare-mono : (x : ℤ) → Hoare-Monotonic _≥ₛ_ (pre x)
        hoare-mono x y1 y0 z0 y1≥y0 z0∈pre = rec squash₁ helper z0∈pre
          where
            helper : (∥ [] ≡ z0 ∥₁) ⊎ (∥ x ∷ y0 ≡ z0 ∥₁) → ∥ Σ (List ℤ) (λ z1 → (z1 ∈ pre x y1) × (z1 ∈ _≥ₛ_ z0)) ∥₁
            helper (_⊎_.inl eq-trunc) = rec squash₁ (λ eq → ∣ [] , ∣ _⊎_.inl ∣ refl ∣₁ ∣₁ , subst (λ w → [] ∈ _≥ₛ_ w) eq (≥ₛ-refl []) ∣₁) eq-trunc
            helper (_⊎_.inr eq-trunc) = rec squash₁ (λ eq → ∣ x ∷ y1 , ∣ _⊎_.inr ∣ refl ∣₁ ∣₁ , subst (λ w → (x ∷ y1) ∈ _≥ₛ_ w) eq (is-mono_∷_ x y1 y0 y1≥y0) ∣₁) eq-trunc

        greedy-proof : foldrM maxPre (return []) ⊑ (minR ∘ prefix)
        greedy-proof = reasoning⊑ (
            foldrM maxPre (return [])

            -- return [] ≡ minR (return []) 
            ≡⟨ cong (λ k → foldrM (λ x → minR ∘ pre x) k) (sym minR-return-[]) ⟩⊑
            foldrM (λ x → minR ∘ pre x) (minR (return []))
            
            -- Greedy Theorem            
            ⊑⟨ incl⊑ (greedy_thm _≥ₛ_ Max≥ₛ pre hoare-mono R-trans-≥ₛ (return [])) ⟩
            minR ∘ foldrM pre (return [])
            
            -- prefix ≡ foldrM pre (return []) 
            ≡⟨ cong (λ k → minR ∘ k) (sym prefix-is-foldrM) ⟩⊑
            (minR ∘ prefix)
            ⊑∎ 

            )

        f<=<s⊑g<=<s : f <=< s ⊑ g <=< s
        f<=<s⊑g<=<s k x x∈fs_k = rec squash₁ (λ { (b , b∈sk , x∈fb) → ∣ b , b∈sk , greedy-proof b x x∈fb ∣₁ }) x∈fs_k

        lem-1 : ∀ k y → y ∈ (g <=< s) k → y ∈ ((_≥ₛ_ °) =<< (f <=< s) k)
        lem-1 k y y∈gs_k = rec squash₁ (λ { (b , b∈sk , y∈gb) → 
                rec squash₁ (λ { (x , x∈fb) → 
                    let 
                        x∈gb = greedy-proof b x x∈fb
                        xRy = minR-minimum (prefix b) x x∈gb y (minR-id (prefix b) y y∈gb)
                    in ∣ x , ∣ b , b∈sk , x∈fb ∣₁ , xRy ∣₁
                }) (hasmin-foldrMx b)
            }) y∈gs_k

        lem-2 : (k y : List ℤ) → y ∈ (f <=< s) k → y ∈ ((_≥ₛ_ °) =<< (m <=< h) k)
        lem-2 [] y y∈fs_[] = 
            let 
                y∈return[] : y ∈ return []
                y∈return[] = subst (λ S → y ∈ S) (ret-left-id [] f) y∈fs_[]
            in rec squash₁ (λ { []≡y → 
                let 
                    z = []
                    z∈mh[] : z ∈ (m <=< h) []
                    z∈mh[] = ∣ [ [] ] , ∣ [] , ∣ refl ∣₁ , y∈[y] [ z ] ∣₁ , ∣ _⊎_.inl ∣ refl ∣₁ ∣₁ ∣₁
                    z≥y : z ∈ _≥ₛ_ y
                    z≥y = subst (λ w → z ∈ _≥ₛ_ w) []≡y (≥ₛ-refl [])
                in ∣ z , z∈mh[] , z≥y ∣₁ 
            }) y∈return[]
        lem-2 (x ∷ xs) y y∈fs_xxs = 
            let 
                path = (=<<-∪-dist-left f (return (x ∷ xs)) (s xs)) ∙ (cong (λ u → u ∪ (f <=< s) xs) (ret-left-id (x ∷ xs) f))
                y∈f_xxs_∪_fs_xs = subst (λ S → y ∈ S) path y∈fs_xxs
            in rec squash₁ helper y∈f_xxs_∪_fs_xs
          where
            helper : (y ∈ f (x ∷ xs)) ⊎ (y ∈ (f <=< s) xs) → y ∈ ((_≥ₛ_ °) =<< (m <=< h) (x ∷ xs))
            helper (_⊎_.inl y∈f_xxs) = 
                rec squash₁ (λ { (ys , ys∈f_xs , y∈maxPre_x_ys) → 
                    let 
                        path-h = scanrM-head-is-foldrM maxPre (return []) xs
                        ys∈map-h = subst (λ S → ys ∈ S) (sym path-h) ys∈f_xs
                    in rec squash₁ (λ { (ls , ls∈hxs , head_ls≡ys) → rec squash₁ (λ head-ls≡ys →
                        let 
                            y∈maxPre_x_head_ls = subst (λ w → y ∈ maxPre x w) (sym head-ls≡ys) y∈maxPre_x_ys
                            ls_xxs = y ∷ ls
                            ls_xxs_∈_h_xxs : ls_xxs ∈ h (x ∷ xs)
                            ls_xxs_∈_h_xxs = ∣ ls , ls∈hxs , ∣ y , y∈maxPre_x_head_ls , y∈[y] ls_xxs ∣₁ ∣₁
                            y∈m_ls_xxs : y ∈ member ls_xxs
                            y∈m_ls_xxs = ∣ _⊎_.inl ∣ refl ∣₁ ∣₁
                            z∈mh_xxs : y ∈ (m <=< h) (x ∷ xs)
                            z∈mh_xxs = ∣ ls_xxs , ls_xxs_∈_h_xxs , y∈m_ls_xxs ∣₁
                        in ∣ y , z∈mh_xxs , ≥ₛ-refl y ∣₁) head_ls≡ys
                    }) ys∈map-h
                }) y∈f_xxs
            helper (_⊎_.inr y∈fs_xs) = 
                rec squash₁ (λ { (z , z∈mh_xs , y≥z) → 
                    rec squash₁ (λ { (ls , ls∈hxs , z∈member_ls) → 
                        rec squash₁ (λ { (z' , z'∈maxPre) → 
                            let 
                                ls_xxs = z' ∷ ls
                                ls_xxs_∈_h_xxs : ls_xxs ∈ h (x ∷ xs)
                                ls_xxs_∈_h_xxs = ∣ ls , ls∈hxs , ∣ z' , z'∈maxPre , y∈[y] ls_xxs ∣₁ ∣₁
                                z∈m_ls_xxs : z ∈ member ls_xxs
                                z∈m_ls_xxs = ∣ _⊎_.inr z∈member_ls ∣₁
                                z∈mh_xxs : z ∈ (m <=< h) (x ∷ xs)
                                z∈mh_xxs = ∣ ls_xxs , ls_xxs_∈_h_xxs , z∈m_ls_xxs ∣₁
                            in ∣ z , z∈mh_xxs , y≥z ∣₁
                        }) (hasmin-pre x (head ls))
                    }) z∈mh_xs
                }) (lem-2 xs y y∈fs_xs)
