{-# OPTIONS --cubical #-}
module Min where

open import Cubical.Foundations.Prelude 
open import Cubical.Data.Sigma.Base using (_×_) 
open import Cubical.HITs.PropositionalTruncation as PT  hiding (map)
open import Cubical.Data.Sum.Base using (_⊎_)
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)

open import Sets
open import Monad_v2

record MinR {ℓ : Level} {Y : Type ℓ} (R : Y → ℙ Y) : Type (ℓ-suc ℓ) where
  field
    -- The minR function itself
    minR : ℙ Y → ℙ Y

    universal-property-⇒ : {X : Type _} → (P f : X → ℙ Y) →
      (P ⊑ minR ∘ f) → ((P ⊑ f) × ((P <=< (f °)) ⊑ R))

    universal-property-⇐ : {X : Type _} → (P f : X → ℙ Y) →
      ((P ⊑ f) × ((P <=< (f °)) ⊑ R)) → (P ⊑ minR ∘ f)

  mf⊑f : {X : Type _} (f : X → ℙ Y) → minR ∘ f ⊑ f
  mf⊑f f = fst (universal-property-⇒ (minR ∘ f) f (⊑-refl (minR ∘ f)))

  minR-preserves-order : {X : Type _} (f g : X → ℙ Y) → f ⊑ g → minR ∘ f ⊑ g
  minR-preserves-order f g f⊑g = ⊑-trans {r = minR ∘ f} {s = f} {t = g} (mf⊑f f) f⊑g

  minR-cancellation : {X : Type _} (f g : X → ℙ Y) → f ⊑ minR ∘ g → f ⊑ g
  minR-cancellation f g f⊑ming = ⊑-trans {r = f} {s = minR ∘ g} {t = g} f⊑ming (mf⊑f g)

  thm1 : {X : Type _} (f : X → ℙ Y) → (minR ∘ f) <=< (f °) ⊑ R
  thm1 f = snd (universal-property-⇒ (minR ∘ f) f (⊑-refl (minR ∘ f)))

  mmf⊑mf : {X : Type _} (f : X → ℙ Y) → minR ∘ minR ∘ f ⊑ minR ∘ f
  mmf⊑mf f = mf⊑f (minR ∘ f)

  mf⊑mmf : {X : Type _} (f : X → ℙ Y) → minR ∘ f ⊑ minR ∘ minR ∘ f
  mf⊑mmf f = universal-property-⇐ (minR ∘ f) (minR ∘ f) (⊑-refl (minR ∘ f) , ⊑-trans {r = (minR ∘ f) <=< ((minR ∘ f) °) } {s = (minR ∘ f) <=< (f °)} {t = R} pf1 (thm1 f))
    where 
      ts : ((minR ∘ f) °) ⊑ (f °)
      ts = °-order-preserving-⇐ (minR ∘ f) f (mf⊑f f)
      pf1 = <=<-monotonic-right (minR ∘ f) ((minR ∘ f) °) (f °) ts

  minR⊑id : minR ⊑ id
  minR⊑id = λ ys y y∈ → mf⊑f (const ys) y y y∈
  -- set property

  set-property-⇒ : (xs ys : ℙ Y) → (ys ⊆ minR xs) → (ys ⊆ xs × (∀ y → y ∈ ys → ∀ x → x ∈ xs → y ∈ R x))
  set-property-⇒ xs ys lhs = (λ x → pf1 x x) , (λ y y∈ x x∈ → snd (universal-property-⇒ (const ys) (const xs) λ _ → lhs) x y ∣ y , x∈ , y∈ ∣₁)
    where
      pf1 = ⊑-trans {r = const ys} {s = const (minR xs)} {t = const xs} (⊆2⊑ ys (minR xs) lhs) (mf⊑f (const xs))
        
  set-property-⇐ : (xs ys : ℙ Y) → ys ⊆ xs → (p : (∀ y → y ∈ ys → ∀ x → x ∈ xs → y ∈ R x)) → (ys ⊆ minR xs)
  set-property-⇐ xs ys ys⊆xs p y y∈ys = 
    universal-property-⇐ {X = Y} (const ys) (const xs) 
      ( (λ _ → ys⊆xs) 
      , (λ y0 y1 q → rec (P.∈-isProp (R y0) y1) (λ { (u , y0∈xs , y1∈ys) → p y1 y1∈ys y0 y0∈xs }) q) 
      ) y y y∈ys

  set-property-elem-⇒ : (y : Y) → (xs : ℙ Y)→ (y ∈ minR xs) → ((y ∈ xs) × (∀ x → x ∈ xs → y ∈ R x))
  set-property-elem-⇒ y xs y∈minxs = ((minR⊑id xs y) y∈minxs) , (λ x x∈xs → snd(set-property-⇒ xs (return y) λ y' y'∈[y] → rec (P.∈-isProp (minR xs) y') (λ eq → subst (λ v → v ∈ minR xs) eq  y∈minxs) y'∈[y]) y (y∈[y] y) x x∈xs)

  minR-property : (xs : ℙ Y) → (minR xs ⊆ xs × (∀ y → y ∈ minR xs → ∀ x → x ∈ xs → y ∈ R x))
  minR-property xs = set-property-⇒ xs (minR xs) (P.⊆-refl (minR xs))

  minR-id : (xs : ℙ Y) → (minR xs ⊆ xs)
  minR-id xs = fst (minR-property xs)

  minR-minimum : (xs : ℙ Y) → (∀ y → y ∈ minR xs → ∀ x → x ∈ xs → y ∈ R x)
  minR-minimum xs = snd (minR-property xs)

  minR-contained : (A : ℙ Y) → ∀ y → y ∈ minR A → y ∈ A
  minR-contained A y y∈minRA = minR-id A y y∈minRA  

  minR-property-⇐ : (xs : ℙ Y) (y : Y) → y ∈ xs → (p : (∀ x → x ∈ xs → y ∈ R x)) → (y ∈ minR xs)
  minR-property-⇐ xs y y∈xs p = set-property-⇐ xs (return y) ([y]⊆xs y xs y∈xs) lem2 y (y∈[y] y)
    where
      [y]⊆xs : (y : Y) → (xs : ℙ Y) →  y ∈ xs → return y ⊆ xs
      [y]⊆xs y xs y∈xs = λ x x₁ → rec (P.∈-isProp xs x) (λ x≡y → subst (λ v → v ∈ xs) x≡y y∈xs) x₁

      lem2 : (y₁ : Y) → y₁ ∈ return y → (x : Y) → x ∈ xs → y₁ ∈ R x
      lem2 = λ y₁ y₁∈y x x∈ → rec (P.∈-isProp (R x) y₁) (λ y₁≡y → subst (λ v → v ∈ R x) y₁≡y (p x x∈)) y₁∈y

  -- from set property to universal-property

  from-set-to-universal⇒ : 
      (set-property-⇒ : (xs ys : ℙ Y) → (ys ⊆ minR xs) → (ys ⊆ xs × (∀ y → y ∈ ys → ∀ x → x ∈ xs → y ∈ R x)))
      → ({X : Type _} → ∀ (P f : X → ℙ Y) → (P ⊑ minR ∘ f) → ((P ⊑ f) × ((P <=< (f °)) ⊑ R ))) -- universal-property-⇒
  from-set-to-universal⇒ set-prop-⇒ P f P⊑minR∘f = let
      P⊑f : P ⊑ f
      P⊑f x = fst (set-prop-⇒ (f x) (P x) (P⊑minR∘f x))
      P<=<f°⊑R : (P <=< (f °)) ⊑ R
      P<=<f°⊑R y = λ y' p → rec (P.∈-isProp (R y) y') (λ {(x , (l , r)) → snd (set-prop-⇒ (f x) (P x) ((P⊑minR∘f x))) y' r y l}) p
    in P⊑f , P<=<f°⊑R

  from-set-to-universal-⇐ : 
      (set-property-⇐ : (xs ys : ℙ Y) → ys ⊆ xs → (p : (∀ y → y ∈ ys → ∀ x → x ∈ xs → y ∈ R x)) → (ys ⊆ minR xs))
      → ({X : Type _} → ∀ (P f : X → ℙ Y) → ((P ⊑ f) × ((P <=< (f °)) ⊑ R )) → (P ⊑ minR ∘ f)) -- universal-property-⇐
  from-set-to-universal-⇐ set-prop-⇐ P f (P⊑f , P<=<f°⊑R) = λ x → set-prop-⇐ (f x) (P x) (P⊑f x) λ y z x₁ z₁ → P<=<f°⊑R x₁ y ∣ x , z₁ , z ∣₁  
  
  minR-conditional-anti-monotonicity : {X : Type _} (f g : X → ℙ Y) → f ⊑ g → minR ∘ g ⊑ f → (minR ∘ g) ⊑ minR ∘ f 
  minR-conditional-anti-monotonicity {X} f g f⊑g min∘g⊑f = universal-property-⇐ (minR ∘ g) f (min∘g⊑f , pf2)
    where      
      lem1 : ((minR ∘ g) <=< (f °)) ⊑ ((minR ∘ g) <=< (g °))
      lem1 = <=<-monotonic-right (minR ∘ g) (f °) (g °) (°-order-preserving-⇒ (f °) (g °) f⊑g)

      pf2 : ((minR ∘ g) <=< (f °)) ⊑ R
      pf2 = ⊑-trans {r = (minR ∘ g) <=< (f °)} {s = (minR ∘ g) <=< (g °)} {t = R} lem1 (thm1 g)


  -- minR-monotonicity' : (xs ys : ℙ Y) → xs ⊆ ys → minR xs ⊆ minR ys -- not hold, larger set would have smaller minimums
  -- minR-monotonicity' xs ys xs⊆ys = {!   !}

  minR-conditional-monotonicity : (xs ys : ℙ Y) 
      → xs ⊆ ys 
      → (p : ∀ y → y ∈ ys → y ∈ ((R °) =<< xs))
      → (R-trans : R-trans R)
      → minR xs ⊆ minR ys
  minR-conditional-monotonicity xs ys xs⊆ys p R-trans x x∈minRxs = 
    minR-property-⇐ ys x x∈ys x-is-bound-for-ys
      where
        x∈xs : x ∈ xs
        x∈xs = minR-id xs x x∈minRxs

        x∈ys : x ∈ ys
        x∈ys = xs⊆ys x x∈xs

        x-is-bound-for-ys : ∀ y' → y' ∈ ys → x ∈ R y'
        x-is-bound-for-ys y' y'∈ys = 
          rec (P.∈-isProp (R y') x) 
              (λ { (x' , x'∈xs , y'∈Rx') → 
                  let 
                    x∈Rx' = minR-minimum xs x x∈minRxs x' x'∈xs
                  in R-trans y' x' x (y'∈Rx') x∈Rx'
                }) 
              (p y' y'∈ys)

  -- [todo] : delete or move it to somewhere 
  uname0 : (A B : ℙ Y) → (f : ℙ Y → ℙ Y) → (∀ X Y → X ⊆ Y → f Y ⊆ f X) → f (A ∪ B) ⊆ (f A ∪ f B)
  uname0 A B f p = λ x z → ∣ _⊎_.inl (p A (A ∪  B) (λ x₁ z₁ → ∣ _⊎_.inl z₁ ∣₁) x z) ∣₁ 


  minR_union_subset : (A B : ℙ Y) → minR (A ∪ B) ⊆ (minR A ∪ minR B)
  minR_union_subset A B y y∈minR_AB =
    let y∈AB : y ∈ (A ∪ B)
        y∈AB = minR-id (A ∪ B) y y∈minR_AB
    in rec (P.∈-isProp (minR A ∪ minR B) y) split-case y∈AB
      where
        split-case : (y ∈ A) ⊎ (y ∈ B) → y ∈ (minR A ∪ minR B)
        split-case (_⊎_.inl y∈A) =
          let
            cond-A : ∀ x → x ∈ A → y ∈ R x
            cond-A x x∈A = minR-minimum (A ∪ B) y y∈minR_AB x ∣ _⊎_.inl x∈A ∣₁
            
            y∈minRA = minR-property-⇐ A y y∈A cond-A
          in ∣ _⊎_.inl y∈minRA ∣₁
        
        split-case (_⊎_.inr y∈B) = 
          let cond-B : ∀ x → x ∈ B → y ∈ R x
              cond-B x x∈B = minR-minimum (A ∪ B) y y∈minR_AB x ∣ _⊎_.inr x∈B ∣₁
              
              y∈minRB = minR-property-⇐ B y y∈B cond-B
          in ∣ _⊎_.inr y∈minRB ∣₁

  left-monot-for-minR : {X Z : Type _} (f : Z → ℙ Y) (g : X → ℙ Z) → ((minR ∘ f) <=< g) ⊑ (f <=< g)
  left-monot-for-minR f g = <=<-monotonic-left g ( minR ∘ f) f (mf⊑f f)

  left-monot-for-minR-un : {X Z : Type _} (f : Z → ℙ Y) (g : X → ℙ Z) → (f ⊑ minR ∘ f) → (f <=< g) ⊑ ((minR ∘ f) <=< g)
  left-monot-for-minR-un f g f⊑minf = <=<-monotonic-left g f (minR ∘ f) f⊑minf

  -- too strong 
  -- minR-monotonicity-2 : (A B : ℙ Y) → (A ⊆ B) →  (p : ∀ x → ∀ y → x ∈ R y) → minR A ⊆ minR B
  -- minR-monotonicity-2 A B A⊆B p =  set-property-⇐ B (minR A) (minR-preserves-order (λ _ → A) (λ _ → B) (λ x x₁ x₂ → A⊆B x₁ x₂) p) (λ x x∈minRA → λ y y∈B → p x y)

  minR-monotonicity-3 : (A B : ℙ Y) → (A ⊆ B) → (p : ∀ x → x ∈ A → ∀ y → y ∈ B → x ∈ R y) → minR A ⊆ minR B
  minR-monotonicity-3 A B A⊆B p = set-property-⇐ B (minR A) (minR-preserves-order (λ _ → A) (λ _ → B) (λ x x₁ x₂ → A⊆B x₁ x₂) p) λ y y∈minRA y' y'∈B → p y (minR-contained A y y∈minRA) y' y'∈B


  minR-<=<-Promotion : {X Z : Type _}  → (f : Z → ℙ Y) → (g : X → ℙ Z) → 
    (hasmin : ∀ z → ∥ Σ Y (λ y' → y' ∈ minR (f z)) ∥₁) → 
    R-trans R → 
    minR ∘ (f <=< g) ≡ minR ∘ ((minR ∘ f) <=< g)
  minR-<=<-Promotion {X} {Z} f g hasmin R-trans = ⊑-extensionality (minR ∘ (f <=< g)) (minR ∘ ((minR ∘ f) <=< g)) (minR-promote-<=<-left f g , (minR-promote-<=<-right f g hasmin))
    where
      minR-promote-<=<-right : {X Z : Type _} (f : Z → ℙ Y) → (g : X → ℙ Z) → (hasmin : ∀ z → ∥ Σ Y (λ y' → y' ∈ minR (f z)) ∥₁)  → minR ∘ ((minR ∘ f) <=< g) ⊑ (minR ∘ (f <=< g))
      minR-promote-<=<-right {X} {Z} f g hasmin x = let 
          
          m = g x
          
          lem-1 : ((minR ∘ f) <=< g) x ⊆ (f <=< g) x
          lem-1 = <=<-monotonic-left g (minR ∘ f) f (mf⊑f f) x -- <=<-monotonic-left {m0 = minR ∘ f} {m1 = f} g (mf⊑f f) x

          t1 : ((R °) =<< ((minR ∘ f) =<< m)) ≡ ((λ x → (R °) =<< ((minR ∘ f) x)) =<< m)
          t1 = >>=-assoc m ((minR ∘ f)) (R °)

          t2 : f ⊑ (λ x → (R °) =<< ((minR ∘ f) x)) → (f =<< m) ⊆ ((λ x → (R °) =<< ((minR ∘ f) x)) =<< m) 
          t2 p = <=<-monotonic-left g f (λ x → (R °) =<< ((minR ∘ f) x)) p x
                  
          t3 : f ⊑ (λ x → (R °) =<< ((minR ∘ f) x))
          t3 z y y∈fz = 
            rec squash₁
                (λ { (u , u∈minfz) → 
                      let 
                        uRy : u ∈ R y
                        uRy = minR-minimum (f z) u u∈minfz y y∈fz

                      in ∣ u , (u∈minfz , uRy) ∣₁ 
                }) 
                (hasmin z) 
          t2-proof : (f =<< m) ⊆ ((λ z' → (R °) =<< ((minR ∘ f) z')) =<< m) 
          t2-proof = <=<-monotonic-left g f (λ z' → (R °) =<< ((minR ∘ f) z')) t3 x 

          lem-2 : (f =<< m) ⊆ ((R °) =<< ((minR ∘ f) =<< m))
          lem-2 = subst (λ S → (f =<< m) ⊆ S) (sym t1) t2-proof
          
        in minR-conditional-monotonicity (((minR ∘ f) <=< g) x) ((f <=< g) x)
          lem-1 lem-2 R-trans
      minR-promote-<=<-left : {X Z : Type _} (f : Z → ℙ Y) → (g : X → ℙ Z) → minR ∘ (f <=< g) ⊑ minR ∘ ((minR ∘ f) <=< g)
      minR-promote-<=<-left  {X} {Z} f g = universal-property-⇐ (minR ∘ (f <=< g)) ((minR ∘ f) <=< g) (lem-1 f g , lem-2 f g)
        where
          lem-1 : {X Z : Type _} (f : Z → ℙ Y) → (g : X → ℙ Z) → minR ∘ (f <=< g) ⊑ ((minR ∘ f) <=< g)
          lem-1 f g x y y∈minR_union = 
            let 
              y∈union = minR-id ((f <=< g) x) y y∈minR_union  -- minR-id ((f <=< g) x) y y∈minR_union
            in rec 
                (P.∈-isProp  (((minR ∘ f) <=< g) x) y) 
                (λ { (z , z∈gx , y∈fz) → 
                  ∣ z , (z∈gx , (minR-property-⇐ (f z) y y∈fz λ y' y'∈fz → 
                  minR-minimum ((f <=< g) x) y y∈minR_union y' ∣ z , (z∈gx , y'∈fz) ∣₁))  ∣₁}) 
                y∈union 
          lem-2 : {X Z : Type _} (f : Z → ℙ Y) → (g : X → ℙ Z) → ((minR ∘ (f <=< g)) <=< (((minR ∘ f) <=< g) °)) ⊑ R
          lem-2 f g y y' p = rec 
            (P.∈-isProp (R y) y') 
            (λ {(x , left-h , right-h) → rec 
                  (P.∈-isProp (R y) y') 
                  (λ {(z , z∈gx , y∈min_fz) → minR-minimum ((f <=< g) x) y' right-h y ∣ z , (z∈gx , minR-id (f z) y y∈min_fz) ∣₁}) 
                  left-h 
                }) 
            p


  ∈-bind-⇒ : {X Z : Type _} → (f : Z → ℙ Y) → (y : Y) → ∀ m → y ∈ f =<< m → ∥ Σ Z (λ x → (x ∈ m) × (y ∈ f x)) ∥₁ 
  ∈-bind-⇒ f y m y∈fm = y∈fm
  
  ∈-bind-⇐ : {X Z : Type _} → (f : Z → ℙ Y) → (y : Y) → ∀ m → ∥ Σ Z (λ x → (x ∈ m) × (y ∈ f x)) ∥₁ → y ∈ f =<< m
  ∈-bind-⇐ f y m p = p