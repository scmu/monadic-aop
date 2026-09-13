{-# OPTIONS --cubical --guardedness #-}
module HasMin where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation as PT hiding (map)
open import Cubical.Data.Sum.Base using (_⊎_; inl; inr)
open import Cubical.Data.Sigma.Base using (_×_; Σ)
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Cubical.Data.List hiding (foldr; rec)
open import Cubical.Data.Empty using (elim*; rec*; ⊥*)
open import Cubical.Data.Bool using (Bool; true; false)

open import Sets
open import Monad_v2
open import Min
open import MonadicList

module HasMinProps {ℓ : Level} {Y : Type ℓ} (R : Y → ℙ Y) 
    (minR-inst : MinR R)
    (R-refl  : ∀ x → x ∈ R x)
    (R-trans : ∀ x y z → x ∈ R y → y ∈ R z → x ∈ R z)
    (R-total : ∀ x y → ∥ (x ∈ R y) ⊎ (y ∈ R x) ∥₁) where

    open MinR minR-inst

    -- The minimum of a singleton set `return y` is just `y`
    hasmin-return : ∀ (y : Y) → ∥ Σ Y (λ y' → y' ∈ minR (return y)) ∥₁
    hasmin-return y = ∣ y , (minR-property-⇐ (return y) y (y∈[y] y) (λ x x∈[y] → 
        rec (P.∈-isProp (R x) y) 
            (λ y≡x → subst (λ v → fst (R v y)) y≡x (R-refl y)) x∈[y])) ∣₁ 

    -- If A and B have minimums, their union A ∪ B also has a minimum
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

    -- If A has a minimum and f is monotonic, f <$> A has a minimum
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

    -- Bind preserves hasmin if f is Hoare-monotonic
    hasmin-bind : (A : ℙ Y) (f : Y → ℙ Y)
        → Hoare-Monotonic R f
        → ∥ Σ Y (λ y → y ∈ minR A) ∥₁
        → (∀ y → y ∈ A → ∥ Σ Y (λ z → z ∈ minR (f y)) ∥₁)
        → ∥ Σ Y (λ z → z ∈ minR (f =<< A)) ∥₁
    hasmin-bind A f f-hoare minA minF = 
        rec squash₁ (λ { (mA , mA∈minA) → 
        rec squash₁ (λ { (m' , m'∈minFmA) → 
            let 
                mA∈A = minR-contained A mA mA∈minA
                m'∈FmA = minR-contained (f mA) m' m'∈minFmA
                m'∈FhA : m' ∈ (f =<< A)
                m'∈FhA = ∣ mA , mA∈A , m'∈FmA ∣₁
                
                lower-bound : ∀ z → z ∈ (f =<< A) → m' ∈ R z
                lower-bound z z∈FhA = 
                    rec (P.∈-isProp (R z) m') (λ { (a , a∈A , z∈Fa) → 
                        let mA∈Ra = minR-minimum A mA mA∈minA a a∈A
                        in rec (P.∈-isProp (R z) m') (λ { (z1 , z1∈FmA , z1∈Rz) → 
                            let m'∈Rz1 = minR-minimum (f mA) m' m'∈minFmA z1 z1∈FmA
                            in R-trans m' z1 z m'∈Rz1 z1∈Rz
                        }) (f-hoare mA a z mA∈Ra z∈Fa)
                    }) z∈FhA
            in ∣ m' , minR-property-⇐ (f =<< A) m' m'∈FhA lower-bound ∣₁
        }) (minF mA (minR-contained A mA mA∈minA))
        }) minA


    -- Sufficient condition for nonemptiness of foldrM f e xs:
    -- e is nonempty and f x y is nonempty for every x and y
    foldrM-nonempty : {X : Type ℓ} (f : X → Y → ℙ Y) (e : ℙ Y)
        → ∥ Σ Y (λ y → y ∈ e) ∥₁
        → (∀ x y → ∥ Σ Y (λ z → z ∈ f x y) ∥₁)
        → (xs : List X)
        → ∥ Σ Y (λ y → y ∈ foldrM f e xs) ∥₁
    foldrM-nonempty f e e-ne f-ne []       = e-ne
    foldrM-nonempty f e e-ne f-ne (x ∷ xs) =
        rec squash₁ (λ { (y , y∈fold) →
        rec squash₁ (λ { (z , z∈fxy) → ∣ z , ∣ y , y∈fold , z∈fxy ∣₁ ∣₁ })
            (f-ne x y) })
            (foldrM-nonempty f e e-ne f-ne xs)

    -- [ Finitely enumerable sets ]

    -- A is finitely enumerable: it is the member set of some list
    Finite : ℙ Y → Type (ℓ-suc ℓ)
    Finite A = ∥ Σ (List Y) (λ ys → A ≡ member ys) ∥₁

    member-++ : (xs ys : List Y) → member (xs ++ ys) ≡ member xs ∪ member ys
    member-++ []       ys = sym (∪-∅-unit-l (member ys))
    member-++ (x ∷ xs) ys =
        cong (return x ∪_) (member-++ xs ys) ∙ sym (∪-assoc (return x) (member xs) (member ys))

    -- Closure properties: these let Finite be discharged for concrete step
    -- functions without ever writing down the enumerating list.
    finite-∅ : Finite ∅
    finite-∅ = ∣ [] , refl ∣₁

    finite-return : (y : Y) → Finite (return y)
    finite-return y = ∣ y ∷ [] , sym (∪-∅-unit-r (return y)) ∣₁

    finite-∪ : (A B : ℙ Y) → Finite A → Finite B → Finite (A ∪ B)
    finite-∪ A B = rec2 squash₁ (λ { (xs , A≡xs) (ys , B≡ys) →
        ∣ xs ++ ys , cong₂ _∪_ A≡xs B≡ys ∙ sym (member-++ xs ys) ∣₁ })

    finite-filt : (p : Y → Bool) (y : Y) → Finite (filt p y)
    finite-filt p y = go (p y) refl
      where
        go : (b : Bool) → p y ≡ b → Finite (filt p y)
        go true  eq = subst Finite (sym (filt-true  p y eq)) (finite-return y)
        go false eq = subst Finite (sym (filt-false p y eq)) finite-∅

    -- The member set of a list has a minimum whenever it is nonempty.
    -- Only R-total is used (via hasmin-union); no decidability of R is needed.
    hasmin-member : (ys : List Y)
        → ∥ Σ Y (λ y → y ∈ member ys) ∥₁
        → ∥ Σ Y (λ y → y ∈ minR (member ys)) ∥₁
    hasmin-member []            ne = rec squash₁ (λ { (y , y∈∅) → elim* y∈∅ }) ne
    hasmin-member (y ∷ [])      _  =
        subst (λ S → ∥ Σ Y (λ y' → y' ∈ minR S) ∥₁) (sym (∪-∅-unit-r (return y))) (hasmin-return y)
    hasmin-member (y ∷ y' ∷ ys) _  =
        hasmin-union (return y) (member (y' ∷ ys)) (hasmin-return y)
            (hasmin-member (y' ∷ ys) ∣ y' , ∣ inl (y∈[y] y') ∣₁ ∣₁)

    -- Every nonempty finitely enumerable set has a minimum
    finite-hasmin : (A : ℙ Y)
        → Finite A
        → ∥ Σ Y (λ y → y ∈ A) ∥₁
        → ∥ Σ Y (λ y → y ∈ minR A) ∥₁
    finite-hasmin A fin ne = rec squash₁ (λ { (ys , A≡ys) →
        subst (λ S → ∥ Σ Y (λ y → y ∈ minR S) ∥₁) (sym A≡ys)
              (hasmin-member ys (subst (λ S → ∥ Σ Y (λ y → y ∈ S) ∥₁) A≡ys ne)) }) fin

    -- Bind preserves finiteness when f is finitely branching
    finite-bind : (f : Y → ℙ Y) (A : ℙ Y)
        → (∀ y → Finite (f y))
        → Finite A
        → Finite (f =<< A)
    finite-bind f A f-fin = rec squash₁ (λ { (ys , A≡ys) →
        subst (λ S → Finite (f =<< S)) (sym A≡ys) (go ys) })
      where
        go : (ys : List Y) → Finite (f =<< member ys)
        go []       = ∣ [] , =<<-∅ f ∣₁
        go (y ∷ ys) =
            rec squash₁ (λ { (zs , fy≡zs) →
            rec squash₁ (λ { (ws , rest≡ws) →
                ∣ zs ++ ws
                , ( =<<-∪-dist-left f (return y) (member ys)
                  ∙ cong₂ _∪_ (ret-left-id y f ∙ fy≡zs) rest≡ws
                  ∙ sym (member-++ zs ws) ) ∣₁
            }) (go ys)
            }) (f-fin y)

    -- foldrM f e xs is finite when e is finite and f is finitely branching
    foldrM-finite : {X : Type ℓ} (f : X → Y → ℙ Y) (e : ℙ Y)
        → Finite e
        → (∀ x y → Finite (f x y))
        → (xs : List X)
        → Finite (foldrM f e xs)
    foldrM-finite f e e-fin f-fin []       = e-fin
    foldrM-finite f e e-fin f-fin (x ∷ xs) =
        finite-bind (f x) (foldrM f e xs) (f-fin x) (foldrM-finite f e e-fin f-fin xs)

    -- Hence foldrM over a finitely branching f has a minimum,
    -- with no assumption on Y beyond R-refl / R-trans / R-total
    hasmin-foldrM-finite : {X : Type ℓ} (f : X → Y → ℙ Y) (e : ℙ Y)
        → Finite e
        → (∀ x y → Finite (f x y))
        → ∥ Σ Y (λ y → y ∈ e) ∥₁
        → (∀ x y → ∥ Σ Y (λ z → z ∈ f x y) ∥₁)
        → (xs : List X)
        → ∥ Σ Y (λ y → y ∈ minR (foldrM f e xs)) ∥₁
    hasmin-foldrM-finite f e e-fin f-fin e-ne f-ne xs =
        finite-hasmin (foldrM f e xs) (foldrM-finite f e e-fin f-fin xs) (foldrM-nonempty f e e-ne f-ne xs)



    -- minR preserves Hoare-monotonicity
    Hoare-Monotonic-minR : (f : Y → ℙ Y)
        → Hoare-Monotonic R f
        → (∀ y → ∥ Σ Y (λ z → z ∈ minR (f y)) ∥₁)
        → Hoare-Monotonic R (minR ∘ f)
    Hoare-Monotonic-minR f f-hoare f-hasmin y1 y0 z0 y1Ry0 z0∈minFy0 = 
        rec squash₁ (λ { (z1' , z1'∈minFy1) → 
            let 
                z0∈Fy0 = minR-contained (f y0) z0 z0∈minFy0
            in rec squash₁ (λ { (z1 , z1∈Fy1 , z1Rz0) → 
                let 
                    z1'Rz1 = minR-minimum (f y1) z1' z1'∈minFy1 z1 z1∈Fy1
                    z1'Rz0 = R-trans z1' z1 z0 z1'Rz1 z1Rz0
                in ∣ z1' , z1'∈minFy1 , z1'Rz0 ∣₁
            }) (f-hoare y1 y0 z0 y1Ry0 z0∈Fy0)
        }) (f-hasmin y1)