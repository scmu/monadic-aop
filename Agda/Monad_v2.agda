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
open import PowersetExt

id : ∀ {l} {X : Set l} → X → X
id x = x

infixr 9 _∘_
_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
     → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g (f x)

_∋_ : ∀ {ℓ} {X : Type ℓ} → ℙ X → X → Type ℓ
A ∋ x = x ∈ A

-- functor

map : ∀ {ℓ} {X Y : Type ℓ} → (X → Y) → ℙ X → ℙ Y
map {ℓ} {X} {Y} f xs y = ∥ Σ X (λ x → (x ∈ xs) × (f x ≡ y)) ∥₁ , squash₁

-- functor laws

map-id : ∀ {ℓ} {X : Type ℓ} → (xs : ℙ X) → map id xs ≡ id xs
map-id xs = funExt (λ x → ⇔toPath 
             (rec (snd (xs x)) λ { (x , x∈xs , eq) → subst (λ w → fst (xs w)) eq x∈xs }) 
              λ x∈xs → ∣ x , x∈xs , refl  ∣₁
              )

map-compose : ∀ {ℓ} {X Y Z : Type ℓ}→ (f : X → Y) → (g : Y → Z)
            → (xs : ℙ X) → map (g ∘ f) xs ≡ map g (map f xs)
map-compose f g xs = funExt λ z → ⇔toPath 
              (rec (snd (map g (map f xs) z)) 
                   λ { (x , x∈xs , eq) → ∣ f x , ∣ x , x∈xs , refl ∣₁ , eq ∣₁ }) 
              λ p → do (y , q , gy≡z) ← p
                       (x , r , fx≡y) ← q 
                       return (x , r , subst (λ w → g w ≡ z) (sym fx≡y) gy≡z)
    where open TruncMonad


-- monad

_>>=_ : ∀ {ℓ} {X Y : Type ℓ} → ℙ X → (X → ℙ Y) → ℙ Y
(_>>=_ {X = X} {Y = Y} xs f) y = ∥ Σ X (λ x → fst (xs x) × fst (f x y)) ∥₁ , squash₁ -- ∥ Σ X (λ x → fst (xs x) × fst (f x y)) ∥₁ , squash₁


return : ∀ {ℓ} {X : Type ℓ} → X → ℙ X
return x x' = ∥ x ≡ x' ∥₁ , squash₁

-- monad laws 

ret-right-id : ∀ {ℓ} {X : Type ℓ} → (m : ℙ X) 
             → (m >>= return) ≡ m
ret-right-id m = funExt λ x → ⇔toPath 
                 (rec (snd (m x)) λ { (x' , x'∈m , eq') → 
                    rec (snd (m x)) (λ eq → subst _ eq x'∈m) eq' })
                  λ x∈m → ∣ x , x∈m , ∣ refl ∣₁ ∣₁ 

ret-left-id : ∀ {ℓ} {X Y : Type ℓ} → (x : X) → (f : X → ℙ Y) 
            → (return x >>= f) ≡ f x 
ret-left-id x f = funExt λ y → ⇔toPath 
  (rec (snd (f x y)) λ {(x' , x'∈ , y∈) → 
    rec (snd (f x y)) (λ eq → subst _ (sym eq) y∈)  x'∈}) 
  λ y∈ → ∣ x , ∣ refl ∣₁ , y∈ ∣₁  

>>=-assoc : ∀ {ℓ} {X Y Z : Type ℓ} → (m : ℙ X) → (f : X → ℙ Y) → (g : Y → ℙ Z)
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

_⊑_ : ∀ {ℓ} → {X Y : Type ℓ} → (X → ℙ Y) → (X → ℙ Y) → Type ℓ
r ⊑ s = ∀ x → r x ⊆ s x

⊑-refl :  ∀ {ℓ} → {X Y : Type ℓ} → (r : X → ℙ Y) → r ⊑ r
⊑-refl = λ r x x₁ z → z

⊑-trans : ∀ {ℓ} {X Y : Type ℓ} {r s t : X → ℙ Y} → r ⊑ s → s ⊑ t → r ⊑ t
⊑-trans = λ r⊑s s⊑t x y y∈rx → s⊑t x y (r⊑s x y y∈rx)

⊑-refl-consequence : ∀ {ℓ} → {X Y : Type ℓ} (A B : X → ℙ Y) → A ≡ B → (A ⊑ B) × (B ⊑ A)
⊑-refl-consequence A B p = subst (A ⊑_) p (⊑-refl A), subst (B ⊑_) (sym p) (⊑-refl B)

⊑-extensionality : ∀ {ℓ} → {X Y : Type ℓ} (A B : X → ℙ Y) → (A ⊑ B) × (B ⊑ A) → A ≡ B
⊑-extensionality A B (φ , ψ) = funExt (λ x → P.⊆-extensionality (A x) (B x) (φ x , ψ x))


_⊒_ : ∀ {ℓ} {X Y : Type ℓ} → (X → ℙ Y) → (X → ℙ Y) → Type ℓ
r ⊒ s = s ⊑ r

⊒-trans : ∀ {ℓ} {X Y : Type ℓ} {r s t : X → ℙ Y} → r ⊒ s → s ⊒ t → r ⊒ t
⊒-trans = λ r⊒s s⊒t x y y∈tx → r⊒s x y (s⊒t x y y∈tx)

⊑-antisym :  ∀ {ℓ} → {X Y : Type ℓ} (f g : X → ℙ Y) → f ⊑ g → g ⊑ f → f ≡ g
⊑-antisym f g f⊑g g⊑f = funExt (λ x → P.⊆-antisym (f x) (g x) (f⊑g x) (g⊑f x)) 

-- ⊓ and ⊔

_⊓_ : ∀ {ℓ} {X Y : Type ℓ} → (X → ℙ Y) → (X → ℙ Y) → (X → ℙ Y)
(r ⊓ s) x = r x ∩ s x

  -- ⊓-universal :  r ⊑ s ⊓ t  ⇔  r ⊑ s  ×  r ⊑ t

⊓-universal-⇒ : ∀ {ℓ} {X Y : Type ℓ} {r s t : X → ℙ Y}
              →  r ⊑ s ⊓ t  →  r ⊑ s × r ⊑ t
⊓-universal-⇒ = λ r⊑s⊓t → (λ x y y∈rx → fst (r⊑s⊓t x y y∈rx)) , λ x y y∈rx → snd (r⊑s⊓t x y y∈rx)

⊓-universal-⇐ : ∀ {ℓ} {X Y : Type ℓ} {r s t : X → ℙ Y}
              →  r ⊑ s × r ⊑ t  →  r ⊑ s ⊓ t
⊓-universal-⇐ = λ r⊑s×r⊑t x y y∈rx → (fst r⊑s×r⊑t x y y∈rx) , (snd r⊑s×r⊑t x y y∈rx)

⊓-monotonic : ∀ {ℓ} {X Y : Type ℓ} {r s t u : X → ℙ Y}
              → r ⊑ t → s ⊑ u → r ⊓ s ⊑ t ⊓ u
⊓-monotonic = λ r⊑t s⊑u x y y∈r⊓s'x → r⊑t x y (fst (y∈r⊓s'x)) , s⊑u x y (snd (y∈r⊓s'x))

_⊔_ : ∀ {ℓ} {X Y : Type ℓ} → (X → ℙ Y) → (X → ℙ Y) → (X → ℙ Y)
(r ⊔ s) x = r x ∪ s x

--    -- ⊔-universal : r ⊔ s ⊑ t  ⇔  r ⊑ t  ×  s ⊑ t

⊔-universal-⇒ : ∀ {ℓ} {X Y : Type ℓ} {r s t : X → ℙ Y}
              → r ⊔ s ⊑ t → r ⊑ t × s ⊑ t
⊔-universal-⇒ = λ r⊔s⊑t → (λ x y y∈rx → r⊔s⊑t x y ∣ _⊎_.inl y∈rx ∣₁) , λ x y y∈sx → r⊔s⊑t x y ∣ _⊎_.inr y∈sx ∣₁

⊔-universal-⇐ : ∀ {ℓ} {X Y : Type ℓ}  {r s t : X → ℙ Y}
              → r ⊑ t × s ⊑ t → r ⊔ s ⊑ t
⊔-universal-⇐ {ℓ} {X} {Y} {r} {s} {t} r⊑t×s⊑t x y c∈r⊔s'b = rec (P.∈-isProp (t x) y) (λ {(_⊎_.inl l) → r⊑t×s⊑t .fst x y l ; (_⊎_.inr r) → r⊑t×s⊑t .snd x y r}) c∈r⊔s'b 

⊔-monotonic : ∀ {ℓ} {X Y : Type ℓ} {r s t u : X → ℙ Y}
              → r ⊑ t → s ⊑ u → r ⊔ s ⊑ t ⊔ u
⊔-monotonic = λ r⊑t s⊑u x y y∈r⊔s'x → rec squash₁ (λ {(_⊎_.inl y∈rx) → ∣ _⊎_.inl (r⊑t x y y∈rx) ∣₁ ; (_⊎_.inr y∈sx) → ∣ _⊎_.inr (s⊑u x y y∈sx) ∣₁ }) y∈r⊔s'x 
  
-- -- other monadic operators

_=<<_ : ∀ {ℓ} {X Y : Type ℓ} → (X → ℙ Y) → ℙ X → ℙ Y 
f =<< m = m >>= f

_<=<_ : ∀ {ℓ} {X Y Z : Type ℓ} → (Y → ℙ Z) → (X → ℙ Y) → (X → ℙ Z)
(f <=< g) x = f =<< g x

_<$>_ : ∀ {ℓ} {X Y : Type ℓ} → (X → Y) → ℙ X → ℙ Y
f <$> m  = m >>= λ x → return (f x)      -- _<$>_ = map

fmap : ∀ {ℓ} {X Y : Type ℓ} → (X → Y) → ℙ X → ℙ Y
fmap f m = m >>= λ x → return (f x)

-- -- monotonicity

<$>-monotonic : ∀ {ℓ} {X Y : Type ℓ} → ∀ {m0 m1 : ℙ X} → (f : X → Y) → m0 ⊆ m1 → (f <$> m0) ⊆ (f <$> m1)
<$>-monotonic {x0} {x1} {m0} {m1} f = λ x x₁ x₂ → rec squash₁ (λ x₃ → ∣ (x₃ .fst) , x (x₃ .fst) (x₃ .snd .fst) , x₃ .snd .snd ∣₁) x₂

>>=-monotonic : ∀ {ℓ} {X Y : Type ℓ} → ∀ {m0 m1 : ℙ X} → (f : X → ℙ Y) → m0 ⊆ m1 → (m0 >>= f) ⊆ (m1 >>= f)
>>=-monotonic {x0} {x1} {m0} {m1} f  = λ x x₁ x₂ → rec squash₁ (λ x₃ → ∣ (x₃ .fst) , x (x₃ .fst) (x₃ .snd .fst) , x₃ .snd .snd ∣₁) x₂

<=<-monotonic-left : ∀ {ℓ} {X Y Z : Type ℓ} → ∀ {m0 m1 : Y → ℙ Z} → (f : X → ℙ Y) → m0 ⊑ m1 → (m0 <=< f) ⊑ (m1 <=< f)
<=<-monotonic-left {Y} {Z} {X} {m0} {m1} f m0⊑m1 x z z∈m0<=<fx = rec squash₁ (λ {(y , y∈fx , z∈m0y) → ∣ y , y∈fx , m0⊑m1 y z z∈m0y ∣₁ }) z∈m0<=<fx

<=<-monotonic-right : ∀ {ℓ} {X Y Z : Type ℓ} → ∀ (m : Y → ℙ Z) → (f g : X → ℙ Y) → f ⊑ g → (m <=< f) ⊑ (m <=< g)
<=<-monotonic-right {Y} {Z} {X} m f g f⊑g x z z∈m<=<fx = rec squash₁ (λ {(y , y∈fx , z∈my) → ∣ y , f⊑g x y y∈fx , z∈my ∣₁}) z∈m<=<fx

=<<-monotonic-right :
  ∀ {ℓ} {X Y : Type ℓ}
  (m0 m1 : ℙ X) →
  (f : X → ℙ Y) →
  m0 ⊆ m1 →
  (f =<< m0) ⊆ (f =<< m1)
=<<-monotonic-right m0 m1 f m0⊆m1 y y∈ = rec squash₁ (λ {(x , x∈m0 , x∈m1) → ∣ x , (m0⊆m1 x x∈m0 , x∈m1) ∣₁}) y∈

=<<-monotonic-left :
  ∀ {ℓ} {X Y : Type ℓ}
  (m : ℙ X) →
  (f g : X → ℙ Y) →
  f ⊑ g →
  (f =<< m) ⊆ (g =<< m)
=<<-monotonic-left  = λ m f g f⊑g y y∈fm → rec squash₁ (λ {(x , x∈m , y∈fx ) → ∣ x , x∈m , f⊑g x y y∈fx ∣₁ }) y∈fm

--   -- converse

_° : ∀ {ℓ} {X Y : Type ℓ} → (X → ℙ Y) → (Y → ℙ X)
(r °) y x = r x y

°-idempotent : ∀ {ℓ} {X Y : Type ℓ} → (r : X → ℙ Y) → (r °) ° ≡ r
°-idempotent r = refl

°-order-preserving-⇒ : ∀ {ℓ} {X Y : Type ℓ} (f g : X → ℙ Y) → (f °) ⊑ (g °) → f ⊑ g
°-order-preserving-⇒  f g p = λ x x₁ x₂ → p x₁ x x₂

°-order-preserving-⇐ : ∀ {ℓ} {X Y : Type ℓ} (f g : X → ℙ Y) → f ⊑ g → (f °) ⊑ (g °)
°-order-preserving-⇐ f g p = λ x x₁ x₂ → p x₁ x x₂


--   -- factor
  
_/_ : ∀ {ℓ} {X Y Z : Type ℓ} → (X → ℙ Z) → (X → ℙ Y) → (Y → ℙ Z)
(t / s) y z = ∥ (∀ x → y ∈ s x → z ∈ t x) ∥₁ , squash₁

/-universal-⇒ : ∀ {ℓ} {X Y Z : Type ℓ} → (r : Y → ℙ Z) → (s : X → ℙ Y) → (t : X → ℙ Z) 
              → r <=< s ⊑ t → r ⊑ t / s
/-universal-⇒ r s t = λ r<=<s⊑t y z z∈ry → ∣ (λ x y∈sx → r<=<s⊑t x z ∣ (y , y∈sx , z∈ry) ∣₁) ∣₁

/-universal-⇐ : ∀ {ℓ} {X Y Z : Type ℓ} → (r : Y → ℙ Z) → (s : X → ℙ Y) → (t : X → ℙ Z) 
              → r ⊑ t / s → r <=< s ⊑ t 
/-universal-⇐ r s t = λ  r⊑t/s x z z∈r<=<s'x → rec (t x z .snd) (λ {(y , y∈sx , z∈ry) → rec (t x z .snd) (λ f → f x y∈sx) (r⊑t/s y z z∈ry) }) z∈r<=<s'x


-- -- <=< properties
R-trans : ∀ {ℓ} {X : Type ℓ} → (R : X → ℙ X) → Type _
R-trans R = ∀ x y z → y ∈ R x → z ∈ R y → z ∈ R x

<=<-refl : ∀ {ℓ} {X : Type ℓ} → (R : X → ℙ X) → (R-trans R) → (R <=< R) ⊑ R
<=<-refl R R-trans x x₁ x₁∈lhs = rec (P.∈-isProp (R x) x₁) (λ { (y , y∈Rx , z∈Ry) → R-trans x y x₁ y∈Rx z∈Ry}) x₁∈lhs

<=<-assoc-left : ∀ {ℓ} {X : Type ℓ} →(R S T : X → ℙ X) → (R <=< S) <=< T ⊑ R <=< (S <=< T)
<=<-assoc-left R S T x x' x'∈lhs = rec squash₁ (λ {(y ,  y∈Tx , x'∈R<=<Sy) → rec squash₁ (λ {(z , z∈Sy , x'∈Rz) → ∣ z , ∣ y , y∈Tx , z∈Sy ∣₁ , x'∈Rz  ∣₁ }) x'∈R<=<Sy }) x'∈lhs

<=<-assoc-right : ∀ {ℓ} {X : Type ℓ} → (R S T : X → ℙ X) → R <=< (S <=< T) ⊑ (R <=< S) <=< T
<=<-assoc-right R S T x x' x'∈lhs = rec squash₁ (λ {(z , z∈S<=<Tx , x'∈Rz) → rec squash₁ (λ z₁ →
     ∣ z₁ .fst , z₁ .snd .fst , ∣ z , z₁ .snd .snd , x'∈Rz ∣₁ ∣₁) z∈S<=<Tx}) x'∈lhs 