{-# OPTIONS --cubical #-}
module Min where

open import Cubical.Foundations.Prelude 
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma.Base using (_×_) 
open import Cubical.Functions.Logic hiding (_⊓_; _⊔_)
open import Cubical.HITs.PropositionalTruncation as PT  hiding (map)
import Cubical.HITs.PropositionalTruncation.Monad as TruncMonad
open import Cubical.Data.Sum.Base using (_⊎_)
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import PowersetExt
open import Agda.Builtin.Unit using (⊤ ; tt)


open import Data.List hiding (foldr)

open import Sets
open import Monad
open import Reasoning
open import Sets
private
  variable
    X Y Z : Type

-- [todo] move to other file
rec-⊆ : {ℓ : Level} → {X : Type ℓ} → {xs ys : ℙ X} → ys ⊆ xs → ∀ x → x ∈ ys → x ∈ xs
rec-⊆  = λ x x₁ x₂ → x x₁ x₂

const : {ℓ : Level} → {Z X : Type ℓ} → (xs : ℙ X) → Z → ℙ X 
const {ℓ} {Z} {X} xs = λ (_ : Z) → xs

record MinR {Y : Set} (R : Y → ℙ Y) : Set₁ where
  field
    -- The minR function itself
    minR : ℙ Y → ℙ Y
    
    -- The universal property
    universal-property-⇒ : {X : Set} → ∀ (P f : X → ℙ Y) →
      (P ⊑ minR ∘ f) →
      ((P ⊑ f) × ((P <=< (f °)) ⊑ R ))
    universal-property-⇐ : {X : Set} → ∀ (P f : X → ℙ Y) →
      ((P ⊑ f) × ((P <=< (f °)) ⊑ R )) → 
      (P ⊑ minR ∘ f)

  minR-monotonicity : {X : Set} (f : X → ℙ Y) → minR ∘ f ⊑ f
  minR-monotonicity {X} f = fst (universal-property-⇒ (minR ∘ f) f (⊑-refl (minR ∘ f)))

  -- [todo] rename may needed
  minR-preserves-order : {X : Set} (f g : X → ℙ Y) → f ⊑ g → minR ∘ f ⊑ g
  minR-preserves-order {X} f g f⊑g = ⊑-trans {r = minR ∘ f} {s = f} {t = g} (minR-monotonicity f) f⊑g

  minR-cancellation : {X : Set} (f g : X → ℙ Y) → f ⊑ minR ∘ g → f ⊑ g
  minR-cancellation {X} f g f⊑ming = ⊑-trans {r = f} {s = minR ∘ g} {t = g} f⊑ming (minR-monotonicity g)

  thm1 : {X : Set} (f : X → ℙ Y) → (minR ∘ f) <=< (f °) ⊑ R
  thm1 {X}  f = snd (universal-property-⇒ (minR ∘ f) f (⊑-refl (minR ∘ f)))

  mmf⊑mf : {X : Set} (f : X → ℙ Y) → minR ∘ minR ∘ f ⊑ minR ∘ f
  mmf⊑mf {X} f = minR-monotonicity (minR ∘ f)

  mf⊑mmf : {X : Set} (f : X → ℙ Y) → minR ∘ f ⊑ minR ∘ minR ∘ f
  mf⊑mmf {X} f = universal-property-⇐ (minR ∘ f) (minR ∘ f) (⊑-refl (minR ∘ f) , ⊑-trans {r = (minR ∘ f) <=< ((minR ∘ f) °) } {s = (minR ∘ f) <=< (f °)} {t = R} pf1 (thm1 f))
    where 
      ts : ((minR ∘ f) °) ⊑ (f °)
      ts = °-order-preserving-⇐ (minR ∘ f) f (minR-monotonicity f)
      pf1 = <=<-monotonic-right (minR ∘ f) ((minR ∘ f) °) (f °) ts

  minR⊑id : minR ⊑ id
  minR⊑id = λ ys y y∈ → minR-monotonicity (const ys) tt y y∈
  
  ⊆2⊑ : {X Z : Set} (f g : ℙ Z) → f ⊆ g → (λ (_ : X) → f) ⊑ (λ (_ : X) → g)
  ⊆2⊑ f g f⊆g = λ x x₁ x₂ → f⊆g x₁ x₂

  -- from universal property to set property

  set-property-⇒ : (xs ys : ℙ Y) → (ys ⊆ minR xs) → (ys ⊆ xs × (∀ y → y ∈ ys → ∀ x → x ∈ xs → y ∈ R x))
  set-property-⇒ xs ys lhs = (λ x → pf1 x x) , (λ y y∈ x x∈ → snd (universal-property-⇒ (const ys) (const xs) λ _ → lhs) x y ∣ y , x∈ , y∈ ∣₁)
    where
      pf1 = ⊑-trans {r = const ys} {s = (λ (_ : Y) → minR xs)} {t = const xs} (⊆2⊑ ys (minR xs) lhs) (minR-monotonicity (const xs))
      
  set-property-⇐ : (xs ys : ℙ Y) → ys ⊆ xs → (p : (∀ y → y ∈ ys → ∀ x → x ∈ xs → y ∈ R x)) → (ys ⊆ minR xs)
  set-property-⇐ xs ys ys⊆xs p = universal-property-⇐ (λ (_ : Agda.Builtin.Unit.⊤) → ys) (λ (_ : Agda.Builtin.Unit.⊤) → xs) ((λ _ y₂ y₂∈ → rec-⊆ {X = Y} {xs = xs} {ys = ys} ys⊆xs y₂ y₂∈) , λ x x₁ x₂ → p x₁ (rec (P.∈-isProp ys x₁) (λ x₃ → x₃ .snd .snd) x₂) x (rec (P.∈-isProp xs x) (λ x₃ → x₃ .snd .fst) x₂)) tt

  -- from set property to universal-property

  from-set-to-universal⇒ : 
      (set-property-⇒ : (xs ys : ℙ Y) → (ys ⊆ minR xs) → (ys ⊆ xs × (∀ y → y ∈ ys → ∀ x → x ∈ xs → y ∈ R x)))
      → ({X : Set} → ∀ (P f : X → ℙ Y) → (P ⊑ minR ∘ f) → ((P ⊑ f) × ((P <=< (f °)) ⊑ R ))) -- universal-property-⇒
  from-set-to-universal⇒ set-prop-⇒ P f P⊑minR∘f = let
      P⊑f : P ⊑ f
      P⊑f x = fst (set-prop-⇒ (f x) (P x) (P⊑minR∘f x))
      P<=<f°⊑R : (P <=< (f °)) ⊑ R
      P<=<f°⊑R y = λ y' p → rec (P.∈-isProp (R y) y') (λ {(x , (l , r)) → snd (set-prop-⇒ (f x) (P x) ((P⊑minR∘f x))) y' r y l}) p
    in P⊑f , P<=<f°⊑R

  from-set-to-universal-⇐ : 
      (set-property-⇐ : (xs ys : ℙ Y) → ys ⊆ xs → (p : (∀ y → y ∈ ys → ∀ x → x ∈ xs → y ∈ R x)) → (ys ⊆ minR xs))
      → ({X : Set} → ∀ (P f : X → ℙ Y) → ((P ⊑ f) × ((P <=< (f °)) ⊑ R )) → (P ⊑ minR ∘ f)) -- universal-property-⇐
  from-set-to-universal-⇐ set-prop-⇐ P f (P⊑f , P<=<f°⊑R) = λ x → set-prop-⇐ (f x) (P x) (P⊑f x) λ y z x₁ z₁ → P<=<f°⊑R x₁ y ∣ x , z₁ , z ∣₁  

  lem : (xs : ℙ Y) → (y₀ y₁ : Y) → y₀ ∈ ((λ _ → xs) °) y₁ → y₁ ∈ xs
  lem = λ xs y₀ y₁ x → x
  
  min-conditional-anti-monotonicity : {X : Set} (f g : X → ℙ Y) → f ⊑ g → minR ∘ g ⊑ f → (minR ∘ g) ⊑ minR ∘ f 
  min-conditional-anti-monotonicity {X} f g f⊑g min∘g⊑f = universal-property-⇐ (minR ∘ g) f (min∘g⊑f , pf2)
    where      
      lem1 : ((minR ∘ g) <=< (f °)) ⊑ ((minR ∘ g) <=< (g °))
      lem1 = <=<-monotonic-right (minR ∘ g) (f °) (g °) (°-order-preserving-⇒ (f °) (g °) f⊑g)

      pf2 : ((minR ∘ g) <=< (f °)) ⊑ R
      pf2 = ⊑-trans {r = (minR ∘ g) <=< (f °)} {s = (minR ∘ g) <=< (g °)} {t = R} lem1 (thm1 g)


  -- [todo] : delete or move it to somewhere 
  uname0 : (A B : ℙ Y) → (f : ℙ Y → ℙ Y) → (∀ X Y → X ⊆ Y → f Y ⊆ f X) → f (A ∪ B) ⊆ (f A ∪ f B)
  uname0 A B f p = λ x z → ∣ _⊎_.inl (p A (A ∪ B) (λ x₁ z₁ → ∣ _⊎_.inl z₁ ∣₁) x z) ∣₁ 

  sbub : {X : Set} → (f g : X → ℙ Y) → ∀ x → (minR (f x) ∪ minR (g x)) ⊆ minR (f x ∪ g x)
  sbub = λ f g x  → set-property-⇐ (f x ∪ g x) (minR (f x) ∪ minR (g x)) {!   !} {!   !}

  aa : (A B : ℙ Y) → (minR A ∪ minR B) ⊆ minR (A ∪ B)
  aa A B = set-property-⇐  (A ∪ B) (minR A ∪ minR B) {!   !} λ y' x y x₂ → rec {!   !} (λ {(_⊎_.inl l) → {!   !} ; (_⊎_.inr r) → {!   !} }) x₂

  sub : (A B : ℙ Y) → minR (A ∪ B) ⊆ (minR A ∪ minR B)
  sub A B = λ y p → uname0 A B minR {!   !} y p

  minR-⋃-dist : (A B : ℙ Y) → minR (A ∪ B) ⊆ minR (minR A ∪ minR B)
  minR-⋃-dist A B = λ x x∈minR_A∪B → set-property-⇐ ((minR A ∪ minR B)) (minR (A ∪ B)) {!   !} (λ y y∈minR_A∪B y' y'∈minRA∪minRB → snd (universal-property-⇒ {! A x  !} {!   !} {!   !}) y' y {!   !}) x x∈minR_A∪B 
  
  
  -- Promotion into Kliseli Composition
  -- minR ∘ (f <=< g) = minR ∘ ((minR  ∘ f) <=< g)

  -- ≡ (h ∘ (f <=< g)) x ⊆  ((h ∘ f) <=< g) x
  -- ≡ h ((f <=< g) x) ⊆  ((h ∘ f) <=< g) x
  -- ≡ h (f =<< g x) ⊆  ((h ∘ f) <=< g) x
  -- ≡ h (f =<< g x) ⊆  (h ∘ f) =<< g x
  -- ≡ h (f =<< g x) ⊆  (h ∘ f) =<< g x
  -- ≡ h {y | z <- g x, y <- f z} ⊆ {y | z <- g x, y <- (h ∘ f) z} ≡ {y | z <- g x, y <- h (f z)}
  -- ≡ h (⋃ {f z | z <- g x}) ⊆ {h (f z) | z <- g x}

  left-monot-for-minR : {X Z : Set} (f : Z → ℙ Y) (g : X → ℙ Z) → ((minR ∘ f) <=< g) ⊑ (f <=< g)
  left-monot-for-minR f g = <=<-monotonic-left {m0 = minR ∘ f} {m1 = f} g (minR-monotonicity f)

  left-monot-for-minR-un : {X Z : Set} (f : Z → ℙ Y) (g : X → ℙ Z) → (f ⊑ minR ∘ f) → (f <=< g) ⊑ ((minR ∘ f) <=< g)
  left-monot-for-minR-un f g f⊑minf = <=<-monotonic-left {m0 = f} {m1 = minR ∘ f} g f⊑minf
  
  test : {X : Set} (f : X → ℙ Y) → f <=< (f °) ⊑ R
  test f = {!   !}
  
  minR-<=<-Promotion  : {X Z : Set} (f : Z → ℙ Y) → (g : X → ℙ Z) → minR ∘ (f <=< g) ≡ minR ∘ ((minR ∘ f) <=< g)
  minR-<=<-Promotion {X} {Z} f g = ⊑-extensionality (minR ∘ (f <=< g)) (minR ∘ ((minR ∘ f) <=< g)) (minR-promote-<=<-left f g , (minR-promote-<=<-right f g))
    where
      minR-promote-<=<-right : {X Z : Set} (f : Z → ℙ Y) → (g : X → ℙ Z) → minR ∘ ((minR ∘ f) <=< g) ⊑ minR ∘ (f <=< g)
      minR-promote-<=<-right {X} {Z} f g = minR-preserves-order ((minR ∘ f) <=< g) (minR ∘ (f <=< g)) (universal-property-⇐ ((minR ∘ f) <=< g) (f <=< g) (left-monot-for-minR f g , {!   !})) 
      -- we need: (((minR ∘ f) <=< g) <=< ((f <=< g) °)) ⊑ R, or ((minR ∘ f) <=< g) ⊑ minR ∘ (f <=< g)

      minR-promote-<=<-left  : {X Z : Set} (f : Z → ℙ Y) → (g : X → ℙ Z) → minR ∘ (f <=< g) ⊑ minR ∘ ((minR ∘ f) <=< g)
      minR-promote-<=<-left  {X} {Z} f g = universal-property-⇐ (minR ∘ (f <=< g)) ((minR ∘ f) <=< g) ({!   !} , {!   !})
      -- we need: minR ∘ (f <=< g) ⊑ ((minR ∘ f) <=< g)
      -- we need: ((minR ∘ (f <=< g)) <=< (((minR ∘ f) <=< g) °)) ⊑ R



foldr : (X → Y → ℙ Y) → ℙ Y → List X → ℙ Y
foldr f e [] = e
foldr f e (x ∷ xs) = f x =<< foldr f e xs

converse-swap : (R : Y → ℙ Z) → (S : X → ℙ Y) → ((R <=< S) °) ⊑ ((S °) <=< (R °)) 
converse-swap R S = λ z x x∈lhs → rec squash₁ (λ {(y , y∈Sx , z∈Ra) → ∣  y , (z∈Ra , y∈Sx) ∣₁}) x∈lhs


⊆to⊆' : {X : Set} → {A B : ℙ X} → A ⊆ B → A ⊆' B
⊆to⊆' {X} {A} {B} A⊆B = incl A B A⊆B


test2 : (f : X → Y → ℙ Y) → (e : ℙ Y) → (x : X) → (xs : List X) → (R : Y → ℙ Y) → (R-trans : R-trans R) → (mr : MinR R)  → (precond : (R <=< (f x °)) ⊑ ((f x °) <=< R)) → ((MinR.minR mr ∘ f x) <=< (MinR.minR mr ∘ foldr f e)) <=< ((f x <=< foldr f e) °) ⊑ R
test2 {X} {Y} f e x xs R R-trans mr precond y = reasoning (
  ⊆begin 
  (((MinR.minR mr ∘ f x) <=< (MinR.minR mr ∘ foldr f e)) <=< ((f x <=< foldr f e) °)) y 
  ⊆⟨ ⊆to⊆'( <=<-monotonic-right ((MinR.minR mr ∘ f x) <=< (MinR.minR mr ∘ foldr f e)) (((f x <=< foldr f e) °)) ((((foldr f e) °) <=< ((f x)°) )) (converse-swap (f x) (foldr f e)) y) ⟩
  (((MinR.minR mr ∘ f x) <=< (MinR.minR mr ∘ foldr f e)) <=< (((foldr f e) °) <=< ((f x)°) )) y
  ⊆⟨ ⊆to⊆' (pf0 y) ⟩ --  (minR · g) <=< g ° ⊆ R
  (((MinR.minR mr ∘ f x) <=< R) <=< (f x °)) y
  ⊆⟨ ⊆to⊆' (pf1 y) ⟩ --  R <=< (f x) ◦ ⊆ (f x) ◦ <=< R
  (((MinR.minR mr ∘ f x) <=< (f x °)) <=< R) y
  ⊆⟨ ⊆to⊆' ((<=<-monotonic-left R (MinR.thm1 mr (f x))) y) ⟩ -- (minR · f x) <=< (f x) ◦ <=< R
  (R <=< R) y
  ⊆⟨ ⊆to⊆' ((<=<-refl R R-trans) y) ⟩ 
  R y
  ⊆∎)
  where
    a = MinR.minR mr ∘ f x
    fx° = f x °
    g = foldr f e
    pf0 : (( a <=< (MinR.minR mr ∘ g)) <=< ((g °) <=< fx°)) ⊑ 
          (( a <=< R) <=< fx°)
    pf0 = ⊑-trans tr1 tr2
      where 
        tr1 : (( a <=< (MinR.minR mr ∘ g)) <=< ((g °) <=< fx°)) ⊑ 
              (( a <=< ((MinR.minR mr ∘ g) <=< (g °))) <=< fx°)
        tr1 = {!  !}
        tr2 : (( a <=< ((MinR.minR mr ∘ g) <=< (g °))) <=< fx°) ⊑ (( a <=< R) <=< fx°)
        tr2 = {!   !}

    pf1 : (((MinR.minR mr ∘ f x) <=< R) <=< (f x °)) ⊑ (((MinR.minR mr ∘ f x) <=< (f x °)) <=< R)
    pf1 = ⊑-trans (⊑-trans trivial trivial2) trivial3
      where
        trivial : (((MinR.minR mr ∘ f x) <=< R) <=< (f x °)) ⊑ (MinR.minR mr ∘ f x) <=< (R <=< (f x °))
        trivial = <=<-assoc-left (MinR.minR mr ∘ f x) R (f x °)
        
        trivial2 : (MinR.minR mr ∘ f x) <=< (R <=< (f x °)) ⊑ (MinR.minR mr ∘ f x) <=< ((f x °) <=< R)
        trivial2 = <=<-monotonic-right (MinR.minR mr ∘ f x) ((R <=< (f x °))) (((f x °) <=< R)) precond

        trivial3 : (MinR.minR mr ∘ f x) <=< ((f x °) <=< R) ⊑ (((MinR.minR mr ∘ f x) <=< (f x °)) <=< R)
        trivial3 = <=<-assoc-right (MinR.minR mr ∘ f x)  (f x °) R
