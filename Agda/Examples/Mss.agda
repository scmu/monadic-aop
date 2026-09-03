{-# OPTIONS --cubical --guardedness #-}
module Examples.Mss where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Cubical.Data.Sigma.Base using (_×_) 
open import Cubical.Data.Sum.Base using (_⊎_) 
open import Cubical.Data.Int
open import Cubical.Data.List hiding (rec; foldr)
open import Cubical.Data.Int.Order as Order using (_≤_; ≤Dec; isTrans≤; isRefl≤; ≤-o+-cancel; ≤-o+; lt; eq; gt; <-weaken)
open import Cubical.Relation.Nullary using (yes; no; Dec; ¬_)
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

-- maxlist/bmax expect a total order in the "≤" sense (R b = down-set of b),
-- which is the converse of _≥ₛ_; and it must be untruncated since maxlist computes with it.
≥ₛ°-total : ∀ x y → (x ∈ (_≥ₛ_ °) y) ⊎ (y ∈ (_≥ₛ_ °) x)
≥ₛ°-total x y with (sumℤ x) Order.≟ (sumℤ y)
... | Order.lt x<y = _⊎_.inl ∣ Order.<-weaken x<y ∣₁
... | Order.eq x≡y = _⊎_.inl ∣ 0 , x≡y ∣₁
... | Order.gt y<x = _⊎_.inr ∣ Order.<-weaken y<x ∣₁

open HasMinProps _≥ₛ_ Max≥ₛ ≥ₛ-refl ≥ₛ-trans ≥ₛ-total


-- lemma for maxlist-⊆-minR

maxlist-in-member : (x : List ℤ) (xs : List (List ℤ)) 
    → maxlist (_≥ₛ_ °) ≥ₛ°-total (x ∷ xs) ∈ member (x ∷ xs)
maxlist-in-member x [] = ∣ _⊎_.inl (y∈[y] x) ∣₁
maxlist-in-member x (y ∷ xs) with ≥ₛ°-total x (maxlist (_≥ₛ_ °) ≥ₛ°-total (y ∷ xs))
... | _⊎_.inl _ = ∣ _⊎_.inr (maxlist-in-member y xs) ∣₁
... | _⊎_.inr _ = ∣ _⊎_.inl (y∈[y] x) ∣₁

maxlist-is-max : (x : List ℤ) (xs : List (List ℤ)) → ∀ z 
    → z ∈ member (x ∷ xs) 
    → maxlist (_≥ₛ_ °) ≥ₛ°-total (x ∷ xs) ∈ _≥ₛ_ z
maxlist-is-max x [] z z∈mem = rec (P.∈-isProp (_≥ₛ_ z) x) helper z∈mem
  where
    helper : (z ∈ return x) ⊎ (z ∈ ∅) → x ∈ _≥ₛ_ z
    helper (_⊎_.inl z∈retx) = rec (P.∈-isProp (_≥ₛ_ z) x) (λ x≡z → subst (λ w → x ∈ _≥ₛ_ w) x≡z (≥ₛ-refl x)) z∈retx
    helper (_⊎_.inr z∈∅) = elim* z∈∅
maxlist-is-max x (y ∷ xs) z z∈mem with ≥ₛ°-total x (maxlist (_≥ₛ_ °) ≥ₛ°-total (y ∷ xs))
... | _⊎_.inl x∈≥maxYs = rec (P.∈-isProp (_≥ₛ_ z) (maxlist (_≥ₛ_ °) ≥ₛ°-total (y ∷ xs))) helper z∈mem
  where
    helper : (z ∈ return x) ⊎ (z ∈ member (y ∷ xs)) → maxlist (_≥ₛ_ °) ≥ₛ°-total (y ∷ xs) ∈ _≥ₛ_ z
    helper (_⊎_.inl z∈retx) = rec (P.∈-isProp (_≥ₛ_ z) (maxlist (_≥ₛ_ °) ≥ₛ°-total (y ∷ xs))) (λ x≡z → subst (λ w → maxlist (_≥ₛ_ °) ≥ₛ°-total (y ∷ xs) ∈ _≥ₛ_ w) x≡z x∈≥maxYs) z∈retx
    helper (_⊎_.inr z∈mem') = maxlist-is-max y xs z z∈mem'
... | _⊎_.inr maxYs∈≥x = rec (P.∈-isProp (_≥ₛ_ z) x) helper z∈mem
  where
    helper : (z ∈ return x) ⊎ (z ∈ member (y ∷ xs)) → x ∈ _≥ₛ_ z
    helper (_⊎_.inl z∈retx) = rec (P.∈-isProp (_≥ₛ_ z) x) (λ x≡z → subst (λ w → x ∈ _≥ₛ_ w) x≡z (≥ₛ-refl x)) z∈retx
    helper (_⊎_.inr z∈mem') = ≥ₛ-trans x (maxlist (_≥ₛ_ °) ≥ₛ°-total (y ∷ xs)) z maxYs∈≥x (maxlist-is-max y xs z z∈mem')

-- return (maxlist xs) ⊆ max⊴ (member xs)
maxlist-⊆-minR : (x : List ℤ) (xs : List (List ℤ)) 
    → return (maxlist (_≥ₛ_ °) ≥ₛ°-total (x ∷ xs)) 
         ⊆ minR (member (x ∷ xs))
maxlist-⊆-minR x xs y y∈ret = rec (P.∈-isProp (minR (member (x ∷ xs))) y)
    (λ max≡y → subst (λ w → w ∈ minR (member (x ∷ xs))) max≡y
        (minR-property-⇐ (member (x ∷ xs)) (maxlist (_≥ₛ_ °) ≥ₛ°-total (x ∷ xs))
            (maxlist-in-member x xs) (maxlist-is-max x xs)))
    y∈ret


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

    -- moand laws
    ≡⟨ cong (λ k → minR ∘ k) (sym (<=<-right-id-pure (member) (scanr zplus []))) ⟩⊑
    minR ∘ (member <=< (return ∘ scanr zplus []))

    ⊑⟨ incl⊑ (minR-conditional-monotonicity-func (m <=< u) (m <=< h) m<=<u⊑m<=<h lem-3 R-trans-≥ₛ) ⟩
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
        u = (return ∘ scanr zplus [])

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

        lem-1 : ∀ k y → y ∈ (g <=< s) k 
                → y ∈ ((_≥ₛ_ °) =<< (f <=< s) k)
        lem-1 k y y∈gs_k = rec squash₁ (λ { (b , b∈sk , y∈gb) → 
                rec squash₁ (λ { (x , x∈fb) → 
                    let 
                        x∈gb = greedy-proof b x x∈fb
                        xRy = minR-minimum (prefix b) x x∈gb y (minR-id (prefix b) y y∈gb)
                    in ∣ x , ∣ b , b∈sk , x∈fb ∣₁ , xRy ∣₁
                }) (hasmin-foldrMx b)
            }) y∈gs_k

        lem-2 : (k y : List ℤ) 
              → y ∈ (f <=< s) k 
              → y ∈ ((_≥ₛ_ °) =<< (m <=< h) k)
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
                -- path : (f =<< (return (x ∷ xs) ∪ s xs)) ≡ f (x ∷ xs) ∪ (f <=< s) xs 
                path = (=<<-∪-dist-left f (return (x ∷ xs)) (s xs)) ∙ (cong (λ u → u ∪ (f <=< s) xs) (ret-left-id (x ∷ xs) f))
                -- (f <=< s) (x ∷ xs) ≡ f (x ∷ xs) ∪ (f <=< s) x
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

        zplus-is-maxPre : ∀ x ys → zplus x ys ∈ maxPre x ys
        zplus-is-maxPre x ys = in-pre , is-max
          where
            in-pre : zplus x ys ∈ pre x ys
            in-pre with ≤Dec (x + sumℤ ys) 0
            ... | yes p = ∣ _⊎_.inl ∣ refl ∣₁ ∣₁
            ... | no p = ∣ _⊎_.inr ∣ refl ∣₁ ∣₁

            is-max : ∀ z → z ∈ pre x ys → fst (_≥ₛ_ z (zplus x ys))
            is-max z z∈pre with ≤Dec (x + sumℤ ys) 0
            ... | yes p = rec squash₁ (λ { (_⊎_.inl z≡[]) → rec squash₁ (λ []≡z → ∣ 0 , subst (λ k → sumℤ k ≡ pos 0) []≡z refl ∣₁) z≡[] ; (_⊎_.inr z≡xys) → rec squash₁ (λ x∷ys≡z → ∣ fst p , subst (λ k → (sumℤ k +pos fst p) ≡ pos 0) x∷ys≡z (snd p) ∣₁) z≡xys }) z∈pre
            ... | no p = rec squash₁ helper' z∈pre
              where
                p' : 0 ≤ (x + sumℤ ys)
                p' with (x + sumℤ ys) Order.≟ pos 0
                ... | Order.lt a<0 = Cubical.Data.Empty.elim (p (Order.<-weaken a<0))
                ... | Order.eq a≡0 = Cubical.Data.Empty.elim (p (subst (λ v → v ≤ pos 0) (sym a≡0) Order.isRefl≤))
                ... | Order.gt a>0 = Order.<-weaken a>0

                helper' : ∥ [] ≡ z ∥₁ ⊎ ∥ x ∷ ys ≡ z ∥₁ → ∥ sumℤ z ≤ x + sumℤ ys ∥₁
                helper' (_⊎_.inl []≡z) = rec squash₁ (λ []≡z → ∣ subst (λ k → sumℤ k ≤ x + sumℤ ys) []≡z p' ∣₁) []≡z
                helper' (_⊎_.inr x∷ys≡z) = rec squash₁ (λ x∷ys≡z → ∣ subst (λ k → sumℤ k ≤ x + sumℤ ys) x∷ys≡z Order.isRefl≤ ∣₁) x∷ys≡z

        zplus-⊑-maxPre : ∀ x → (return ∘ zplus x) ⊑ maxPre x
        zplus-⊑-maxPre x ys y y∈ret = rec (P.∈-isProp (maxPre x ys) y) (λ y≡zplus → subst (λ w → w ∈ maxPre x ys) y≡zplus (zplus-is-maxPre x ys)) y∈ret

        m<=<u⊑m<=<h : (m <=< u) ⊑ (m <=< h)
        m<=<u⊑m<=<h = <=<-monotonic-right m u h (pure-scanr-⊑-scanrM zplus maxPre [] zplus-⊑-maxPre)

        
        ¬≤0→0≤ : (v : ℤ) → ¬ (v ≤ 0) → 0 ≤ v
        ¬≤0→0≤ v p with v Order.≟ pos 0
        ... | Order.lt v<0 = Cubical.Data.Empty.elim (p (Order.<-weaken v<0))
        ... | Order.eq v≡0 = Cubical.Data.Empty.elim (p (subst (λ w → w ≤ pos 0) (sym v≡0) Order.isRefl≤))
        ... | Order.gt v>0 = Order.<-weaken v>0

        -- sumℤ (zplus x ys) is always max 0 (x + sumℤ ys)
        zplus-sum : ∀ x ys → sumℤ (zplus x ys) ≡ max 0 (x + sumℤ ys)
        zplus-sum x ys with ≤Dec (x + sumℤ ys) 0
        ... | yes p = sym (maxComm 0 (x + sumℤ ys) ∙ Order.≤→max p)
        ... | no ¬p = sym (Order.≤→max (¬≤0→0≤ (x + sumℤ ys) ¬p))

        zplus-mono : ∀ (x : ℤ) (ys zs : List ℤ)
            → sumℤ ys ≤ sumℤ zs
            → sumℤ (zplus x ys) ≤ sumℤ (zplus x zs)
        zplus-mono x ys zs ys≤zs =
            subst2 _≤_ (sym (zplus-sum x ys)) (sym (zplus-sum x zs)) mono
          where
            mono : max 0 (x + sumℤ ys) ≤ max 0 (x + sumℤ zs)
            mono = Order.≤MonotoneMax {m = 0} {n = 0} Order.isRefl≤ (≤-o+ {o = x} ys≤zs)

        scanrM-head-≤-pure : ∀ (xs : List ℤ) (ls_xs : List (List ℤ))
            → ls_xs ∈ scanrM maxPre (return []) xs
            → sumℤ (head ls_xs) ≤ sumℤ (head (scanr zplus [] xs))
        scanrM-head-≤-pure [] ls_xs ls_xs∈h[] =
            rec Order.isProp≤ (λ { (e , e∈[] , wrape≡ls-trunc) →
                rec Order.isProp≤ (λ wrape≡ls →
                    rec Order.isProp≤ (λ []≡e →
                        let
                            wrap[]≡ls : wrap [] ≡ ls_xs
                            wrap[]≡ls = cong wrap []≡e ∙ wrape≡ls
                        in subst (λ w → sumℤ (head w) ≤ sumℤ (head (scanr zplus [] []))) wrap[]≡ls Order.isRefl≤
                    ) e∈[]
                ) wrape≡ls-trunc
            }) ls_xs∈h[]
        scanrM-head-≤-pure (x ∷ xs) ls_xs ls_xs∈h_xxs =
            rec Order.isProp≤ (λ { (ys , ys∈hxs , c) →
            rec Order.isProp≤ (λ { (z , z∈maxPre , z∷ys≡ls_xs-trunc) →
            rec Order.isProp≤ (λ z∷ys≡ls_xs →
                let
                    qs = scanr zplus [] xs

                    z∈pre : z ∈ pre x (head ys)
                    z∈pre = minR-id (pre x (head ys)) z z∈maxPre

                    z≤zplus : sumℤ z ≤ sumℤ (zplus x (head ys))
                    z≤zplus = rec Order.isProp≤ id ((zplus-is-maxPre x (head ys)) .snd z z∈pre)

                    ih : sumℤ (head ys) ≤ sumℤ (head qs)
                    ih = scanrM-head-≤-pure xs ys ys∈hxs

                    mono : sumℤ (zplus x (head ys)) ≤ sumℤ (zplus x (head qs))
                    mono = zplus-mono x (head ys) (head qs) ih

                    head-ls_xs≡z : head ls_xs ≡ z
                    head-ls_xs≡z = cong head (sym z∷ys≡ls_xs)
                in subst (λ w → sumℤ w ≤ sumℤ (zplus x (head qs))) (sym head-ls_xs≡z) (isTrans≤ z≤zplus mono)
            ) z∷ys≡ls_xs-trunc
            }) c
            }) ls_xs∈h_xxs
        
        scanrM-≥-pure : ∀ xs ls
            → ls ∈ scanrM maxPre (return []) xs
            → ∀ y → y ∈ member ls
            → ∥ Σ (List ℤ) (λ z → (z ∈ member (scanr zplus [] xs)) × (sumℤ y ≤ sumℤ z))  ∥₁
        scanrM-≥-pure [] ls ls∈h[] y y∈mem = rec squash₁ (λ {(e , e∈[] , ls∈[[]]) → rec squash₁ (λ [e]≡ls → rec squash₁ (λ []≡e → 
            let
                ls≡[[]] : ls ≡ [ [] ] 
                ls≡[[]] = subst (λ w → ls ≡ wrap w) (sym []≡e) (sym [e]≡ls)

                y∈ret[]∪∅ : y ∈ return [] ∪ ∅
                y∈ret[]∪∅ = subst (λ w → y ∈ member w) ls≡[[]] y∈mem 
                
                y∈ret[] : y ∈ return []
                y∈ret[] = subst (λ w → y ∈ w) (return-∪-∅ []) y∈ret[]∪∅
            in 
                rec squash₁ (λ []≡y → ∣ [] , (∣ _⊎_.inl (y∈[y] []) ∣₁ , (0 , subst (λ w → sumℤ w ≡ pos 0) []≡y refl)) ∣₁) y∈ret[])
            e∈[]) ls∈[[]]}) ls∈h[]
        scanrM-≥-pure (x ∷ xs) ls ls∈h_xxs y y∈mem = 
            rec squash₁ (λ { (ls_xs , ls_xs∈hxs , c) → 
            rec squash₁ (λ { (z' , z'∈maxPre , ls∈z'∷ls_xs) → 
            rec squash₁ (λ z'∷ls_xs≡ls → 
                let
                    -- qs = scanr zplus [] xs                    
                    y∈mem' : y ∈ member (z' ∷ ls_xs)
                    y∈mem' = subst (λ w → y ∈ member w) (sym z'∷ls_xs≡ls) y∈mem                    
                in rec squash₁ (λ {
                    -- Case 1: y = z'
                    (_⊎_.inl y≡z') →
                        rec squash₁ (λ y≡z'↓ →
                            let
                                qs = scanr zplus [] xs

                                z'∈pre : z' ∈ pre x (head ls_xs)
                                z'∈pre = minR-id (pre x (head ls_xs)) z' z'∈maxPre

                                z'≤zplus : sumℤ z' ≤ sumℤ (zplus x (head ls_xs))
                                z'≤zplus = rec Order.isProp≤ id ((zplus-is-maxPre x (head ls_xs)) .snd z' z'∈pre)

                                ih : sumℤ (head ls_xs) ≤ sumℤ (head qs)
                                ih = scanrM-head-≤-pure xs ls_xs ls_xs∈hxs

                                mono : sumℤ (zplus x (head ls_xs)) ≤ sumℤ (zplus x (head qs))
                                mono = zplus-mono x (head ls_xs) (head qs) ih

                                y≤zplus : sumℤ y ≤ sumℤ (zplus x (head qs))
                                y≤zplus = subst (λ w → sumℤ w ≤ sumℤ (zplus x (head qs))) y≡z'↓ (isTrans≤ z'≤zplus mono)

                                z∈scanr-mem : (zplus x (head qs)) ∈ member (scanr zplus [] (x ∷ xs))
                                z∈scanr-mem = ∣ _⊎_.inl (y∈[y] (zplus x (head qs))) ∣₁
                            in ∣ zplus x (head qs) , z∈scanr-mem , y≤zplus ∣₁
                        ) y≡z'
                    ;
                    -- Case 2: y ∈ member ls_xs, IH
                    (_⊎_.inr y∈ls_xs) → 
                        rec squash₁ (λ { (z , z∈qs , y≤z) → 
                            ∣ z , ∣ _⊎_.inr z∈qs ∣₁ , y≤z ∣₁
                        }) (scanrM-≥-pure xs ls_xs ls_xs∈hxs y y∈ls_xs)
                }) y∈mem'
            ) ls∈z'∷ls_xs
            }) c
            }) ls∈h_xxs
        
        lem-3 : (m <=< h) ⊑ ((_≥ₛ_ °) <=< (m <=< u))
        lem-3 k y y∈mh_k = 
            rec squash₁ (λ { (ls , ls∈hk , y∈mem_ls) → 
                rec squash₁ (λ {(z , z∈mem_u , y≤z) → 
                    ∣ z , (∣ scanr zplus [] k , ∣ refl ∣₁ , z∈mem_u ∣₁ , ∣ y≤z ∣₁) ∣₁}) 
                    (scanrM-≥-pure k ls ls∈hk y y∈mem_ls)
            }) y∈mh_k

