{-# OPTIONS --cubical #-}
module Monad_v2 where

open import Cubical.Foundations.Prelude 
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma.Base using (_×_) 
open import Cubical.Functions.Logic hiding (_⊓_; _⊔_)
open import Cubical.HITs.PropositionalTruncation as PT  hiding (map)
import Cubical.HITs.PropositionalTruncation.Monad as TruncMonad
open import Cubical.Data.Sum.Base using (_⊎_)
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Sets
-- open import PowersetExt
open import Cubical.Data.Empty using (isProp⊥; isProp⊥* ; ⊥* ; elim*)

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    X : Type ℓ₁
    Y : Type ℓ₂
    Z : Type ℓ₃

∅ : ℙ X
∅ x = ⊥* , isProp⊥*

id : ∀ {l} {X : Set l} → X → X
id x = x

infixr 9 _∘_
_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
     → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g (f x)

_∋_ : ∀ {ℓ} {X : Type ℓ} → ℙ X → X → Type ℓ
A ∋ x = x ∈ A

-- functor

map : {X Y : Type ℓ} → (X → Y) → ℙ X → ℙ Y
map f xs y = ∥ Σ _ (λ x → (x ∈ xs) × (f x ≡ y)) ∥₁ , squash₁

-- functor laws

map-id : (xs : ℙ X) → map id xs ≡ id xs
map-id xs = funExt (λ x → ⇔toPath 
             (rec (snd (xs x)) λ { (x , x∈xs , eq) → subst (λ w → fst (xs w)) eq x∈xs }) 
              λ x∈xs → ∣ x , x∈xs , refl  ∣₁
              )

map-compose : {X Y Z : Type ℓ}→ (f : X → Y) → (g : Y → Z)
            → (xs : ℙ X) → map (g ∘ f) xs ≡ map g (map f xs)
map-compose f g xs = funExt λ z → ⇔toPath 
              (rec (snd (map g (map f xs) z)) 
                   λ { (x , x∈xs , eq) → ∣ f x , ∣ x , x∈xs , refl ∣₁ , eq ∣₁ }) 
              λ p → do (y , q , gy≡z) ← p
                       (x , r , fx≡y) ← q 
                       return (x , r , subst (λ w → g w ≡ z) (sym fx≡y) gy≡z)
    where open TruncMonad


-- monad

_>>=_ : {X Y : Type ℓ} → ℙ X → (X → ℙ Y) → ℙ Y
(xs >>= f) y = ∥ Σ _ (λ x → fst (xs x) × fst (f x y)) ∥₁ , squash₁


return : X → ℙ X
return x x' = ∥ x ≡ x' ∥₁ , squash₁

-- monad laws 

ret-right-id : (m : ℙ X) → (m >>= return) ≡ m
ret-right-id m = funExt λ x → ⇔toPath 
                 (rec (snd (m x)) λ { (x' , x'∈m , eq') → 
                    rec (snd (m x)) (λ eq → subst _ eq x'∈m) eq' })
                  λ x∈m → ∣ x , x∈m , ∣ refl ∣₁ ∣₁ 

ret-left-id : {X Y : Type ℓ} → (x : X) → (f : X → ℙ Y) 
            → (return x >>= f) ≡ f x 
ret-left-id x f = funExt λ y → ⇔toPath 
  (rec (snd (f x y)) λ {(x' , x'∈ , y∈) → 
    rec (snd (f x y)) (λ eq → subst _ (sym eq) y∈)  x'∈}) 
  λ y∈ → ∣ x , ∣ refl ∣₁ , y∈ ∣₁  

>>=-assoc : {X Y Z : Type ℓ} → (m : ℙ X) → (f : X → ℙ Y) → (g : Y → ℙ Z)
          → (m >>= f) >>= g ≡ m >>= (λ x → f x >>= g)
>>=-assoc m f g = funExt λ z → ⇔toPath 
  (rec (snd ((m >>= (λ x → f x >>= g)) z)) 
    (λ { (y , y∈ , z∈) → rec (snd ((m >>= (λ x → f x >>= g)) z)) 
           (λ {(x , x∈ , y∈) → ∣ x , x∈ , ∣ y , y∈ , z∈ ∣₁ ∣₁}) y∈})) 
  (rec (snd (((m >>= f) >>= g) z)) 
    λ {(x , x∈ , z∈) → rec (snd (((m >>= f) >>= g) z)) 
      (λ {(y , y∈ , z∈) → ∣ y , ∣ x , x∈ , y∈ ∣₁ , z∈ ∣₁}) z∈})  

-- set monad

-- ⊑ and ⊒

infixr 6 _⊑_ _⊒_

_⊑_ : (X → ℙ Y) → (X → ℙ Y) → Type _
r ⊑ s = ∀ x → r x ⊆ s x

⊑-refl : (r : X → ℙ Y) → r ⊑ r
⊑-refl r x x₁ z = z

⊑-trans : {r s t : X → ℙ Y} → r ⊑ s → s ⊑ t → r ⊑ t
⊑-trans r⊑s s⊑t x y y∈rx = s⊑t x y (r⊑s x y y∈rx)

⊑-refl-consequence : (A B : X → ℙ Y) → A ≡ B → (A ⊑ B) × (B ⊑ A)
⊑-refl-consequence A B p = subst (A ⊑_) p (⊑-refl A) , subst (B ⊑_) (sym p) (⊑-refl B)

⊑-extensionality : (A B : X → ℙ Y) → (A ⊑ B) × (B ⊑ A) → A ≡ B
⊑-extensionality A B (φ , ψ) = funExt (λ x → P.⊆-extensionality (A x) (B x) (φ x , ψ x))

_⊒_ : (X → ℙ Y) → (X → ℙ Y) → Type _
r ⊒ s = s ⊑ r

⊒-trans : {r s t : X → ℙ Y} → r ⊒ s → s ⊒ t → r ⊒ t
⊒-trans r⊒s s⊒t x y y∈tx = r⊒s x y (s⊒t x y y∈tx)

⊑-antisym : (f g : X → ℙ Y) → f ⊑ g → g ⊑ f → f ≡ g
⊑-antisym f g f⊑g g⊑f = funExt (λ x → P.⊆-antisym (f x) (g x) (f⊑g x) (g⊑f x))
-- ⊓ and ⊔

_⊓_ : (X → ℙ Y) → (X → ℙ Y) → (X → ℙ Y)
(r ⊓ s) x = r x ∩ s x

⊓-universal-⇒ : {r s t : X → ℙ Y}
              →  r ⊑ s ⊓ t  →  r ⊑ s × r ⊑ t
⊓-universal-⇒ r⊑s⊓t = (λ x y y∈rx → fst (r⊑s⊓t x y y∈rx)) , λ x y y∈rx → snd (r⊑s⊓t x y y∈rx)

⊓-universal-⇐ : {r s t : X → ℙ Y}
              →  r ⊑ s × r ⊑ t  →  r ⊑ s ⊓ t
⊓-universal-⇐ r⊑s×r⊑t x y y∈rx = (fst r⊑s×r⊑t x y y∈rx) , (snd r⊑s×r⊑t x y y∈rx)

⊓-monotonic : {r s t u : X → ℙ Y}
              → r ⊑ t → s ⊑ u → r ⊓ s ⊑ t ⊓ u
⊓-monotonic r⊑t s⊑u x y y∈r⊓s'x = r⊑t x y (fst y∈r⊓s'x) , s⊑u x y (snd y∈r⊓s'x)

_⊔_ : (X → ℙ Y) → (X → ℙ Y) → (X → ℙ Y)
(r ⊔ s) x = r x ∪ s x

--    -- ⊔-universal : r ⊔ s ⊑ t  ⇔  r ⊑ t  ×  s ⊑ t
  
⊔-universal-⇒ : {r s t : X → ℙ Y}
              → r ⊔ s ⊑ t → r ⊑ t × s ⊑ t
⊔-universal-⇒ = λ r⊔s⊑t → (λ x y y∈rx → r⊔s⊑t x y ∣ _⊎_.inl y∈rx ∣₁) , λ x y y∈sx → r⊔s⊑t x y ∣ _⊎_.inr y∈sx ∣₁

⊔-universal-⇐ : (r s t : X → ℙ Y)
              → r ⊑ t × s ⊑ t → r ⊔ s ⊑ t
⊔-universal-⇐ r s t r⊑t×s⊑t x y c∈r⊔s'b = rec (P.∈-isProp (t x) y) (λ {(_⊎_.inl l) → r⊑t×s⊑t .fst x y l ; (_⊎_.inr r) → r⊑t×s⊑t .snd x y r}) c∈r⊔s'b 

⊔-monotonic : {r s t u : X → ℙ Y}
              → r ⊑ t → s ⊑ u → r ⊔ s ⊑ t ⊔ u
⊔-monotonic = λ r⊑t s⊑u x y y∈r⊔s'x → rec squash₁ (λ {(_⊎_.inl y∈rx) → ∣ _⊎_.inl (r⊑t x y y∈rx) ∣₁ ; (_⊎_.inr y∈sx) → ∣ _⊎_.inr (s⊑u x y y∈sx) ∣₁ }) y∈r⊔s'x 
  
-- other monadic operators

_=<<_ : {X Y : Type ℓ} → (X → ℙ Y) → ℙ X → ℙ Y 
f =<< m = m >>= f

_<=<_ : {X Y Z : Type ℓ} → (Y → ℙ Z) → (X → ℙ Y) → (X → ℙ Z)
(f <=< g) x = f =<< g x

_<$>_ : {X Y : Type ℓ} → (X → Y) → ℙ X → ℙ Y
f <$> m  = m >>= λ x → return (f x)      -- _<$>_ = map

_>>_ : {X Y : Type ℓ} → ℙ X → ℙ Y → ℙ Y
m >> n = m >>= (λ _ → n)

_<<_ : {X Y : Type ℓ} → ℙ X → ℙ Y → ℙ X
m << n = m >>= (λ x → n >>= λ _ → return x)


fmap : {X Y : Type ℓ} → (X → Y) → ℙ X → ℙ Y
fmap f m = m >>= λ x → return (f x)

-- monotonicity

<$>-monotonic : {X Y : Type ℓ} → (f : X → Y) → (xs ys : ℙ X) → xs ⊆ ys → (f <$> xs) ⊆ (f <$> ys)
<$>-monotonic f xs ys xs⊆ys y y∈ = 
  rec squash₁ (λ { (x , x∈xs , fx≡y) → ∣ x , xs⊆ys x x∈xs , fx≡y ∣₁ }) y∈

>>=-monotonic : {X Y : Type ℓ} → (f : X → ℙ Y) → (xs ys : ℙ X) → xs ⊆ ys → (xs >>= f) ⊆ (ys >>= f)
>>=-monotonic f xs ys xs⊆ys y y∈ = 
  rec squash₁ (λ { (x , x∈xs , y∈fx) → ∣ x , xs⊆ys x x∈xs , y∈fx ∣₁ }) y∈

=<<-monotonic-right : {X Y : Type ℓ} → (f : X → ℙ Y) → (xs ys : ℙ X) → xs ⊆ ys → (f =<< xs) ⊆ (f =<< ys)
=<<-monotonic-right f xs ys xs⊆ys y y∈ = 
  rec squash₁ (λ { (x , x∈xs , y∈fx) → ∣ x , xs⊆ys x x∈xs , y∈fx ∣₁ }) y∈

=<<-monotonic-left : {X Y : Type ℓ} → (xs : ℙ X) → (f₁ f₂ : X → ℙ Y) → f₁ ⊑ f₂ → (f₁ =<< xs) ⊆ (f₂ =<< xs)
=<<-monotonic-left xs f₁ f₂ f₁⊑f₂ y y∈ = 
  rec squash₁ (λ { (x , x∈xs , y∈f₁x) → ∣ x , x∈xs , f₁⊑f₂ x y y∈f₁x ∣₁ }) y∈

<=<-monotonic-left : {X Y Z : Type ℓ} → (f : X → ℙ Y) → (g₁ g₂ : Y → ℙ Z) → g₁ ⊑ g₂ → (g₁ <=< f) ⊑ (g₂ <=< f)
<=<-monotonic-left f g₁ g₂ g₁⊑g₂ x z z∈ = 
  rec squash₁ (λ { (y , y∈fx , z∈g₁y) → ∣ y , y∈fx , g₁⊑g₂ y z z∈g₁y ∣₁ }) z∈

<=<-monotonic-right : {X Y Z : Type ℓ} → (g : Y → ℙ Z) → (f₁ f₂ : X → ℙ Y) → f₁ ⊑ f₂ → (g <=< f₁) ⊑ (g <=< f₂)
<=<-monotonic-right g f₁ f₂ f₁⊑f₂ x z z∈ = 
  rec squash₁ (λ { (y , y∈f₁x , z∈gy) → ∣ y , f₁⊑f₂ x y y∈f₁x , z∈gy ∣₁ }) z∈

-- converse

_° : {X Y : Type ℓ} → (X → ℙ Y) → (Y → ℙ X)
(r °) y x = r x y

°-idempotent : {X Y : Type ℓ} → (r : X → ℙ Y) → (r °) ° ≡ r
°-idempotent r = refl

°-order-preserving-⇒ : {X Y : Type ℓ} → (f g : X → ℙ Y) → (f °) ⊑ (g °) → f ⊑ g
°-order-preserving-⇒ f g p x x₁ x₂ = p x₁ x x₂

°-order-preserving-⇐ : {X Y : Type ℓ} → (f g : X → ℙ Y) → f ⊑ g → (f °) ⊑ (g °)
°-order-preserving-⇐ f g p x x₁ x₂ = p x₁ x x₂

--   -- factor
  
_/_ : {X Y Z : Type ℓ} → (X → ℙ Z) → (X → ℙ Y) → (Y → ℙ Z)
(t / s) y z = ∥ (∀ x → y ∈ s x → z ∈ t x) ∥₁ , squash₁

/-universal-⇒ : {X Y Z : Type ℓ} → (r : Y → ℙ Z) → (s : X → ℙ Y) → (t : X → ℙ Z) → r <=< s ⊑ t → r ⊑ t / s
/-universal-⇒ r s t r<=<s⊑t y z z∈ry = ∣ (λ x y∈sx → r<=<s⊑t x z ∣ (y , y∈sx , z∈ry) ∣₁) ∣₁

/-universal-⇐ : {X Y Z : Type ℓ} → (r : Y → ℙ Z) → (s : X → ℙ Y) → (t : X → ℙ Z) → r ⊑ t / s → r <=< s ⊑ t 
/-universal-⇐ r s t r⊑t/s x z z∈r<=<s'x = rec (t x z .snd) (λ {(y , y∈sx , z∈ry) → rec (t x z .snd) (λ f → f x y∈sx) (r⊑t/s y z z∈ry) }) z∈r<=<s'x


-- <=< properties
R-trans : {X : Type ℓ} → (R : X → ℙ X) → Type ℓ
R-trans R = ∀ x y z → y ∈ R x → z ∈ R y → z ∈ R x

<=<-refl : {X : Type ℓ} → (R : X → ℙ X) → (R-trans R) → (R <=< R) ⊑ R
<=<-refl R R-trans x x₁ x₁∈lhs = rec (P.∈-isProp (R x) x₁) (λ { (y , y∈Rx , z∈Ry) → R-trans x y x₁ y∈Rx z∈Ry}) x₁∈lhs

<=<-assoc-left : {X : Type ℓ} → (R S T : X → ℙ X) → (R <=< S) <=< T ⊑ R <=< (S <=< T)
<=<-assoc-left R S T x x' x'∈lhs = rec squash₁ (λ {(y ,  y∈Tx , x'∈R<=<Sy) → rec squash₁ (λ {(z , z∈Sy , x'∈Rz) → ∣ z , ∣ y , y∈Tx , z∈Sy ∣₁ , x'∈Rz  ∣₁ }) x'∈R<=<Sy }) x'∈lhs

<=<-assoc-right : {X : Type ℓ} → (R S T : X → ℙ X) → R <=< (S <=< T) ⊑ (R <=< S) <=< T
<=<-assoc-right R S T x x' x'∈lhs = rec squash₁ (λ {(z , z∈S<=<Tx , x'∈Rz) → rec squash₁ (λ z₁ → ∣ z₁ .fst , z₁ .snd .fst , ∣ z , z₁ .snd .snd , x'∈Rz ∣₁ ∣₁) z∈S<=<Tx}) x'∈lhs

-- <$> properties
=<<-<$>-fusion : {X Y Z : Type ℓ} → (f : Y → ℙ Z) → (g : X → Y) → (xs : ℙ X) 
               → f =<< (g <$> xs) ≡ (f ∘ g) =<< xs 
=<<-<$>-fusion f g xs = 
  >>=-assoc xs (λ x → return (g x)) f 
  ∙ cong (λ k → xs >>= k) (funExt λ x → ret-left-id (g x) f)

-- non-determinism monad

-- (λ x → f x ∪ g x) =<< m ≡ (f =<< m) ∪ (g =<< m)
=<<-∪-dist-right : {X Y : Type ℓ} → (f g : X → ℙ Y) → (m : ℙ X) 
                 → ((λ x → f x ∪ g x) =<< m) ≡ ((f =<< m) ∪ (g =<< m))
=<<-∪-dist-right f g m = P.⊆-extensionality _ _ (lhs , rhs)
  where
    lhs : ((λ x → f x ∪ g x) =<< m) ⊆ ((f =<< m) ∪ (g =<< m))
    lhs y y∈L = rec squash₁ (λ { (x , x∈m , y∈f∪g) → 
      rec squash₁ (λ { (_⊎_.inl y∈f) → ∣ _⊎_.inl ∣ x , x∈m , y∈f ∣₁ ∣₁
                     ; (_⊎_.inr y∈g) → ∣ _⊎_.inr ∣ x , x∈m , y∈g ∣₁ ∣₁ }) y∈f∪g }) y∈L

    rhs : ((f =<< m) ∪ (g =<< m)) ⊆ ((λ x → f x ∪ g x) =<< m)
    rhs y y∈R = rec squash₁ (λ { 
      (_⊎_.inl y∈fm) → rec squash₁ (λ { (x , x∈m , y∈f) → ∣ x , x∈m , ∣ _⊎_.inl y∈f ∣₁ ∣₁ }) y∈fm ; 
      (_⊎_.inr y∈gm) → rec squash₁ (λ { (x , x∈m , y∈g) → ∣ x , x∈m , ∣ _⊎_.inr y∈g ∣₁ ∣₁ }) y∈gm }) y∈R

=<<-∪-dist-left : {X Y : Type ℓ} → (f : X → ℙ Y) → (m n : ℙ X) 
                → (f =<< (m ∪ n)) ≡ ((f =<< m) ∪ (f =<< n))
=<<-∪-dist-left f m n = P.⊆-extensionality _ _ (lhs , rhs)
  where
    lhs : (f =<< (m ∪ n)) ⊆ ((f =<< m) ∪ (f =<< n))
    lhs y y∈L = rec squash₁ (λ { (x , x∈m∪n , y∈f) → 
      rec squash₁ (λ { (_⊎_.inl x∈m) → ∣ _⊎_.inl ∣ x , x∈m , y∈f ∣₁ ∣₁
                     ; (_⊎_.inr x∈n) → ∣ _⊎_.inr ∣ x , x∈n , y∈f ∣₁ ∣₁ }) x∈m∪n }) y∈L

    rhs : ((f =<< m) ∪ (f =<< n)) ⊆ (f =<< (m ∪ n))
    rhs y y∈R = rec squash₁ (λ { 
      (_⊎_.inl y∈fm) → rec squash₁ (λ { (x , x∈m , y∈f) → ∣ x , ∣ _⊎_.inl x∈m ∣₁ , y∈f ∣₁ }) y∈fm ; 
      (_⊎_.inr y∈fn) → rec squash₁ (λ { (x , x∈n , y∈f) → ∣ x , ∣ _⊎_.inr x∈n ∣₁ , y∈f ∣₁ }) y∈fn }) y∈R

=<<-∅ : {X Y : Type ℓ} → (f : X → ℙ Y) → (f =<< ∅) ≡ ∅
=<<-∅ f = P.⊆-extensionality _ _ (lhs , rhs)
  where
    lhs : (f =<< ∅) ⊆ ∅
    lhs y y∈L = rec isProp⊥* (λ { (x , x∈∅ , y∈f) → elim* x∈∅ }) y∈L

    rhs : ∅ ⊆ (f =<< ∅)
    rhs y y∈∅ = elim* y∈∅

>>-∅ : {X Y : Type ℓ} → (m : ℙ X) → (m >> (∅ {ℓ} {Y})) ≡ ∅
>>-∅ m = P.⊆-extensionality _ _ (lhs , rhs)
  where
    lhs : (m >> ∅) ⊆ ∅
    lhs y y∈L = rec isProp⊥* (λ { (x , x∈m , y∈∅) → elim* y∈∅ }) y∈L
    
    rhs : ∅ ⊆ (m >> ∅)
    rhs y y∈∅ = elim* y∈∅

∅-<< : {X Y : Type ℓ} → (m : ℙ Y) → ((∅ {ℓ} {X}) << m) ≡ ∅
∅-<< m = P.⊆-extensionality _ _ (lhs , rhs)
  where
    lhs : (∅ << m) ⊆ ∅
    lhs x x∈L = rec isProp⊥* (λ { (x' , x∈∅ , _) → elim* x∈∅ }) x∈L

    rhs : ∅ ⊆ (∅ << m)
    rhs x x∈∅ = elim* x∈∅

-- m ⊆ n → f =<< m ⊆ f =<< n
=<<-⊆-right : {X Y : Type ℓ} → (m n : ℙ X) → (f : X → ℙ Y)
            → m ⊆ n → (f =<< m) ⊆ (f =<< n)
=<<-⊆-right m n f m⊆n y y∈fm = 
  rec squash₁ (λ { (x , x∈m , y∈fx) → ∣ x , m⊆n x x∈m , y∈fx ∣₁ }) y∈fm

-- f ⊑ g → f =<< m ⊆ g =<< m
=<<-⊑-left : {X Y : Type ℓ} → (f g : X → ℙ Y) → (m : ℙ X)
           → f ⊑ g → (f =<< m) ⊆ (g =<< m)
=<<-⊑-left f g m f⊑g y y∈fm = 
  rec squash₁ (λ { (x , x∈m , y∈fx) → ∣ x , x∈m , f⊑g x y y∈fx ∣₁ }) y∈fm


-- [ Helper Functions ]

const : ℙ Y → X → ℙ Y
const ys _ = ys

⊆2⊑ : (xs ys : ℙ Y) → xs ⊆ ys → const {X = X} xs ⊑ const ys
⊆2⊑ xs ys xs⊆ys _ = xs⊆ys

y∈[y] : (y : Y) → y ∈ return y
y∈[y] y = ∣ refl ∣₁

singleton_sub_elem : (A : ℙ Y) → (y : Y) → (return y ⊆ A) → y ∈ A
singleton_sub_elem A y p = p y (y∈[y] y)

elem_subset_singleton : (A : ℙ Y) → (y : Y) → y ∈ A → (return y ⊆ A) 
elem_subset_singleton A y y∈A = λ x x∈[y] → rec (P.∈-isProp A x) (λ eq → subst (λ v → v ∈ A) eq y∈A) x∈[y]

return-∪-∅ : (x : X) → return x ∪ ∅ ≡ return x
return-∪-∅ x = P.⊆-antisym _ _ (λ x₁ x₂ → rec squash₁ (λ { (_⊎_.inl ev) → ev ; (_⊎_.inr no) → elim* no }) x₂) 
  (⊆-∪-left (return x) ∅)
