{-# OPTIONS --cubical --guardedness #-}
module MonadicList where

open import Cubical.Data.List hiding (foldr; rec)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path using (inspect; [_]ᵢ)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Cubical.Data.Sigma.Base using (_×_) 
open import Cubical.Data.Sum.Base using (_⊎_)
open import Cubical.Data.Empty using (isProp⊥; isProp⊥* ; ⊥* ; elim*; ⊥; rec*)
import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Bool.Properties using (true≢false; false≢true)
open import Reasoning

open import Monad_v2
open import Sets
  
private
    variable
        ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
        A : Type ℓ₁
        B : Type ℓ₂
        C : Type ℓ₃
        X : Type ℓ₄

-- fold

foldrM : (A → B → ℙ B) → ℙ B → List A → ℙ B
foldrM f e []       = e 
foldrM f e (x ∷ xs) = f x =<< foldrM f e xs

foldr : (A → B → B) → B → List A → B
foldr f e []       = e 
foldr f e (x ∷ xs) = f x (foldr f e xs)

-- prefix and suffix

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

-- list operations 
wrap : X → List X
wrap x = [ x ]
 
NonEmpty : List X → Type₀
NonEmpty []      = ⊥
NonEmpty (_ ∷ _) = Unit

head : (xs : List X) → NonEmpty xs → X
head []       ()
head (x ∷ xs) _ = x

-- monadic function apply on head of list
onHead : {X Y : Type ℓ} → (X → ℙ Y) → List X → ℙ Y
onHead g []            = ∅
onHead g xs@(_ ∷ _)    = g (head xs tt)

-- monadic head
headM : List X → ℙ X
headM = onHead return

-- onHead can be replaced by head if the list is non-empty
onHead-head : {X Y : Type ℓ} (g : X → ℙ Y) (xs : List X) (ne : NonEmpty xs)
            → onHead g xs ≡ g (head xs ne)
onHead-head g (x ∷ xs) _ = refl

-- onHead is equivalent to headM
onHead-headM : {X Y : Type ℓ} (g : X → ℙ Y) (xs : List X)
             → onHead g xs ≡ (g =<< headM xs)
onHead-headM g []       = sym (=<<-∅ g)
onHead-headM g (x ∷ xs) = sym (ret-left-id x g)

-- replace the old `=<<-<$>-fusion`
onHead-=<< : {X Y : Type ℓ} (g : X → ℙ Y) (m : ℙ (List X))
           → (onHead g =<< m) ≡ (g =<< (headM =<< m))
onHead-=<< g m = cong (λ k → k =<< m) (funExt (λ xs → onHead-headM g xs))
               ∙ sym (>>=-assoc m headM g)

onHead-⊆ : {X Y : Type ℓ} (g h : X → ℙ Y) → g ⊑ h → ∀ xs → onHead g xs ⊆ onHead h xs
onHead-⊆ g h g⊑h []       = λ y y∈ → y∈
onHead-⊆ g h g⊑h (x ∷ xs) = g⊑h x

member : List X → ℙ X
member [] = ∅
member (x ∷ xs) = return x ∪ member xs

bmax : (R : X → ℙ X)
        → (x y : X) 
        → (x ∈ R y) ⊎ (y ∈ R x)
        → X
bmax R x y (_⊎_.inl x≤y) = y
bmax R x y (_⊎_.inr y≤x) = x 


maxlist : (R : X → ℙ X)
        → (total : ∀ x y → (x ∈ R y) ⊎ (y ∈ R x))
        → (xs : List X) 
        → NonEmpty xs 
        → X
maxlist R total []              ()
maxlist R total (x ∷ [])        _ = x
maxlist R total (x ∷ y ∷ xs)    _ =
  bmax R x (maxlist R total (y ∷ xs) tt) (total x (maxlist R total (y ∷ xs) tt))

filt : (p : X → Bool) (x : X) → ℙ X
filt p x with p x
... | true  = return x 
... | false = ∅

filt-true : {X : Type ℓ} (p : X → Bool) (x : X) → p x ≡ true → filt p x ≡ return x
filt-true p x eq with p x
... | true  = refl
... | false = Cubical.Data.Empty.rec (false≢true eq)

filt-false : {X : Type ℓ} (p : X → Bool) (x : X) → p x ≡ false → filt p x ≡ ∅
filt-false p x eq with p x
... | true  = Cubical.Data.Empty.rec (true≢false eq)
... | false = refl

filt-⊆ : {X : Type ℓ} (p : X → Bool) (S : ℙ X) → (filt p =<< S) ⊆ S
filt-⊆ p S z z∈ = rec (P.∈-isProp S z) helper z∈
  where
    helper : Σ _ (λ y → (y ∈ S) × (z ∈ filt p y)) → z ∈ S
    helper (y , y∈S , z∈fpy) with p y | inspect p y
    ... | true  | [ eq ]ᵢ = rec (P.∈-isProp S z) (λ y≡z → subst (λ v → v ∈ S) y≡z y∈S) z∈fpy
    ... | false | [ eq ]ᵢ = rec* z∈fpy

-- scan

scanr : (A → B → B) → B → List A → List B
scanr-NonEmpty : (f : A → B → B) (e : B) (xs : List A) → NonEmpty (scanr f e xs)

scanr f e [] = [ e ]
scanr f e (x ∷ xs) = f x (head qs (scanr-NonEmpty f e xs)) ∷ qs
    where qs = scanr f e xs

scanr-NonEmpty f e []       = tt
scanr-NonEmpty f e (x ∷ xs) = tt

scanrM : (A → B → ℙ B) → ℙ B → List A → ℙ (List B)
scanrM f e [] = wrap <$> e
scanrM f e (x ∷ xs) = do
    ys ← scanrM f e xs
    z ← onHead (f x) ys
    return (z ∷ ys)

isPropNonEmpty : (xs : List X) → isProp (NonEmpty xs)
isPropNonEmpty []      = isProp⊥
isPropNonEmpty (_ ∷ _) = isPropUnit

scanrM-NonEmpty : ∀ {ℓ} {A B : Type ℓ} (f : A → B → ℙ B) (e : ℙ B) (xs : List A)
                → (ls : List B) → ls ∈ scanrM f e xs → NonEmpty ls
scanrM-NonEmpty f e [] ls ls∈ =
  rec (isPropNonEmpty ls)
      (λ { (b , _ , eq) → rec (isPropNonEmpty ls) (λ p → subst NonEmpty p tt) eq }) ls∈
scanrM-NonEmpty f e (x ∷ xs) ls ls∈ =
  rec (isPropNonEmpty ls)
      (λ { (ys , _ , q) → rec (isPropNonEmpty ls)
        (λ { (z , _ , eq) → rec (isPropNonEmpty ls) (λ p → subst NonEmpty p tt) eq }) q }) ls∈

-- fold properties
foldrM-fixed-point-properties-⇐ :
  (f : A → B → ℙ B)
  → (e : ℙ B)
  → (h : List A → ℙ B)
  → (base : e ⊆ h [])
  → (step : ∀ x xs → (f x =<< h xs) ⊆ h (x ∷ xs))
  → foldrM f e ⊑ h
foldrM-fixed-point-properties-⇐ f e h base step [] b b∈fold = base b b∈fold
foldrM-fixed-point-properties-⇐ f e h base step (x ∷ xs) b b∈fold = 
    let 
        -- goal b ∈ h (x ∷ xs)
        -- 1. b ∈ (f x =<< h xs)
        -- 2. step x xs b : b ∈ (f x =<< h xs) → b ∈ h (x ∷ xs)
        lem : b ∈ (f x =<< h xs)
        lem = rec squash₁ (λ {(b' , (b'∈fold , b∈fxb') ) → ∣ b' , foldrM-fixed-point-properties-⇐ f e h base step xs b' b'∈fold , b∈fxb' ∣₁ }) b∈fold
    in step x xs b lem

foldrM-fixed-point-properties-⇒ :
  (f : A → B → ℙ B)
  → (e : ℙ B)
  → (h : List A → ℙ B)
  → (base : h [] ⊆ e)
  → (step : ∀ x xs → h (x ∷ xs) ⊆ (f x =<< h xs))
  → h ⊑ foldrM f e
foldrM-fixed-point-properties-⇒ f e h base step [] b b∈h[] = base b b∈h[]
foldrM-fixed-point-properties-⇒ f e h base step (x ∷ xs) b b∈hxss = 
    let 
        ind : (f x =<< h xs) ⊆ (f x =<< foldrM f e xs) 
        ind = =<<-monotonic-right (f x) (h xs) (foldrM f e xs) (foldrM-fixed-point-properties-⇒  f e h base step xs)
        trans = P.⊆-trans (h (x ∷ xs)) (f x =<< h xs) (f x =<< foldrM f e xs) (step x xs) ind
    in trans b b∈hxss

foldrM-fixed-point-properties-eq⇒ : 
  (f : A → B → ℙ B)
  → (e : ℙ B)
  → (h : List A → ℙ B)
  → (h ≡ foldrM f e) → (h [] ≡ e) × (∀ x → ∀ xs →  (h (x ∷ xs)) ≡ f x =<< h xs )
foldrM-fixed-point-properties-eq⇒ f e h eq = (p1 , p2)
    where
        p1 : h [] ≡ e
        p1 = λ i → eq i []

        p2 : ∀ x xs → h (x ∷ xs) ≡ f x =<< h xs
        p2 x xs = (λ i → eq i (x ∷ xs)) ∙ (λ i → f x =<< eq (~ i) xs)

foldrM-fixed-point-properties-eq⇐ : 
  (f : A → B → ℙ B)
  → (e : ℙ B)
  → (h : List A → ℙ B)
  → (h [] ≡ e) × (∀ x → ∀ xs →  (h (x ∷ xs)) ≡ f x =<< h xs )
  → (h ≡ foldrM f e)
foldrM-fixed-point-properties-eq⇐ f e h (p1 , p2) = funExt lemma
    where
      lemma : ∀ xs → h xs ≡ foldrM f e xs
      lemma [] = p1
      lemma (x ∷ xs) = 
        h (x ∷ xs) 
          ≡⟨ p2 x xs ⟩ 
        (f x =<< h xs) 
          ≡⟨ cong (λ u → f x =<< u) (lemma xs) ⟩ 
        (f x =<< foldrM f e xs) 
          ≡⟨ refl ⟩ 
        foldrM f e (x ∷ xs) 
          ∎

foldrM-fusion :
    (g : A → B → ℙ B)
    → (f : A → B → ℙ B)
    → (e : ℙ B)
    → (h : ℙ B → ℙ B) 
    → (p : ∀ x m → (g x =<< h m) ⊆ h (f x =<< m))
    →  foldrM g (h e) ⊑ h ∘ foldrM f e
foldrM-fusion g f e h p [] b q = q
foldrM-fusion g f e h p (y ∷ ys) b q = 
    let
        ind : (g y =<< foldrM g (h e) ys) ⊆ (g y =<< (h ∘ foldrM f e) ys)
        ind = =<<-monotonic-right (g y) (foldrM g (h e) ys) ((h ∘ foldrM f e) ys) (foldrM-fusion g f e h p ys) 

        trans = P.⊆-trans (g y =<< foldrM g (h e) ys) (g y =<< (h ∘ foldrM f e) ys) (h (foldrM f e (y ∷ ys)))
                ind (p y (foldrM f e ys)) b q
    in trans
        
    
foldrM-monotonic :
    (f₀ : A → B → ℙ B)
    → (f₁ : A → B → ℙ B)
    → (e₀ : ℙ B)
    → (e₁ : ℙ B)
    → (f₀⊑f₁ : ∀ x → f₀ x ⊑ f₁ x)
    → e₀ ⊆ e₁
    → foldrM f₀ e₀ ⊑ foldrM f₁ e₁
foldrM-monotonic f₀ f₁ e₀ e₁ f₀⊑f₁ e₀⊆e₁ [] = e₀⊆e₁
foldrM-monotonic f₀ f₁ e₀ e₁ f₀⊑f₁ e₀⊆e₁ (x ∷ xs) = 
    foldrM-fixed-point-properties-⇐ 
        f₀ e₀ (foldrM f₁ e₁) e₀⊆e₁ 
        (λ x' xs' → =<<-monotonic-left (foldrM f₁ e₁ xs') (f₀ x') (f₁ x') (f₀⊑f₁ x')) 
        (x ∷ xs)



foldrM-pure :
  (f : A → B → B)
  → (e : B)
  → (return ∘ (foldr f e)) ≡ foldrM (λ x → return ∘ f x) (return e)
foldrM-pure f e = funExt (λ x → help x) 
    where
        help : ∀ x → (return ∘ (foldr f e)) x ≡ foldrM (λ x → return ∘ f x) (return e) x
        help []       = refl
        help (x ∷ xs) = 
            return (f x (foldr f e xs))
                ≡⟨ refl ⟩
            (return ∘ f x) (foldr f e xs)
                ≡⟨ sym (ret-left-id (foldr f e xs) (return ∘ f x)) ⟩
            (return ∘ f x) =<< (return ∘ (foldr f e)) xs
                ≡⟨ cong (λ u → (return ∘ f x) =<< u) (help xs) ⟩
            (return ∘ f x) =<< foldrM (λ x → return ∘ f x) (return e) (xs)
                ≡⟨ refl ⟩
            foldrM (λ x → return ∘ f x) (return e) (x ∷ xs)
                ∎
-- scan properties

--  scanrM can be defined in terms of a foldrM:

scanrM-pure-set : 
  (f : A → B → B)
  → (e : B)
  → ∀ xs 
  → (return ∘ (scanr f e)) xs ≡ scanrM (λ x → return ∘ f x) (return e) xs 
scanrM-pure-set f e [] = 
    return [ e ]
    ≡⟨ sym (ret-left-id e (λ x → return [ x ])) ⟩
    (return e >>= (λ x → return [ x ]))
    ≡⟨ refl ⟩
    scanrM (λ x → return ∘ f x) (return e) []
    ∎
scanrM-pure-set f e (x ∷ xs) = 
    let 
        qs = scanr f e xs
        ne = scanr-NonEmpty f e xs
        mf = (λ x → return ∘ f x)
        me = return e
    in 
    (return ∘ scanr f e) (x ∷ xs)

    ≡⟨ refl ⟩
    return (f x (head qs ne) ∷ qs)

    ≡⟨ sym (ret-left-id (f x (head qs ne)) (λ z → return (z ∷ qs))) ⟩
    ((λ z → return (z ∷ qs)) =<< return (f x (head qs ne)))

    ≡⟨ refl ⟩
    ((λ z → return (z ∷ qs)) =<< mf x (head qs ne))

    -- qs is non-empty, so onHead (mf x) qs is mf x (head qs ne)
    ≡⟨ cong (λ u → (λ z → return (z ∷ qs)) =<< u) (sym (onHead-head (mf x) qs ne)) ⟩
    ((λ z → return (z ∷ qs)) =<< onHead (mf x) qs)

    ≡⟨ sym (ret-left-id qs (λ ys → (λ z → return (z ∷ ys)) =<< onHead (mf x) ys)) ⟩
    ((λ ys → (λ z → return (z ∷ ys)) =<< onHead (mf x) ys) =<< return qs)

    -- induction
    ≡⟨ cong (λ k → (λ ys → (λ z → return (z ∷ ys)) =<< onHead (mf x) ys) =<< k) (scanrM-pure-set f e xs) ⟩
    (λ ys → (λ z → return (z ∷ ys)) =<< onHead (mf x) ys) =<< scanrM mf me xs

    ≡⟨ refl ⟩
    scanrM mf me (x ∷ xs)
    ∎ 

scanrM-pure-func :
  (f : A → B → B)
  → (e : B)
  → (return ∘ (scanr f e)) ≡ scanrM (λ x → return ∘ f x) (return e)
scanrM-pure-func f e = funExt (λ x → scanrM-pure-set f e x)

scanrM-monotonic :
    (f₀ : A → B → ℙ B)
    → (f₁ : A → B → ℙ B)
    → (e₀ : ℙ B)
    → (e₁ : ℙ B)
    → (f₀⊑f₁ : ∀ x → f₀ x ⊑ f₁ x)
    → e₀ ⊆ e₁
    → scanrM f₀ e₀ ⊑ scanrM f₁ e₁
scanrM-monotonic f₀ f₁ e₀ e₁ f₀⊑f₁ e₀⊆e₁ [] = <$>-monotonic wrap e₀ e₁ e₀⊆e₁
scanrM-monotonic f₀ f₁ e₀ e₁ f₀⊑f₁ e₀⊆e₁ (x ∷ xs) = 
    let 
        ih = scanrM-monotonic f₀ f₁ e₀ e₁ f₀⊑f₁ e₀⊆e₁ xs
    in
    reasoning⊆ (
        ⊆begin
        scanrM f₀ e₀ (x ∷ xs)
        ≡⟨ refl ⟩⊆
        (scanrM f₀ e₀ xs >>= λ ys → onHead (f₀ x) ys >>= λ z → return (z ∷ ys))
        ⊆⟨ incl (=<<-monotonic-right (λ ys → onHead (f₀ x) ys >>= λ z → return (z ∷ ys)) (scanrM f₀ e₀ xs) (scanrM f₁ e₁ xs) ih) ⟩
        (scanrM f₁ e₁ xs >>= λ ys → onHead (f₀ x) ys >>= λ z → return (z ∷ ys))
        ⊆⟨ incl (=<<-monotonic-left (scanrM f₁ e₁ xs) (λ ys → onHead (f₀ x) ys >>= λ z → return (z ∷ ys)) (λ ys → onHead (f₁ x) ys >>= λ z → return (z ∷ ys)) 
             (λ ys → >>=-monotonic (λ z → return (z ∷ ys)) (onHead (f₀ x) ys) (onHead (f₁ x) ys) (onHead-⊆ (f₀ x) (f₁ x) (f₀⊑f₁ x) ys))) ⟩
        (scanrM f₁ e₁ xs >>= λ ys → onHead (f₁ x) ys >>= λ z → return (z ∷ ys))
        ≡⟨ refl ⟩⊆
        scanrM f₁ e₁ (x ∷ xs)
        ⊆∎
    )

pure-scanr-⊑-scanrM :
  (f : A → B → B)
  → (g : A → B → ℙ B)
  → (e : B)
  → (p : ∀ x → (return ∘ (f x)) ⊑ g x)
  → (return ∘ (scanr f e)) ⊑ scanrM g (return e)
pure-scanr-⊑-scanrM f g e p = reasoning⊑ (
    ⊑begin 
    return ∘ (scanr f e)
    ≡⟨ scanrM-pure-func f e ⟩⊑  
    scanrM (λ x → return ∘ f x) (return e)
    ⊑⟨ incl⊑ ((scanrM-monotonic (λ x → return ∘ f x) g (return e) (return e) p (P.⊆-refl (return e)))) ⟩  
    scanrM g (return e) 
    ⊑∎)

scanrM-⊑-pure-scanr :
  (f : A → B → B)
  → (g : A → B → ℙ B)
  → (e : B)
  → (p : ∀ x →  g x ⊑ return ∘ f x)
  → scanrM g (return e) ⊑ (return ∘ (scanr f e))
scanrM-⊑-pure-scanr f g e p = reasoning⊑ (
    ⊑begin 
    scanrM g (return e)
    ⊑⟨ incl⊑ (scanrM-monotonic g (λ x → return ∘ f x) (return e) (return e) p (P.⊆-refl (return e))) ⟩
    scanrM (λ x → return ∘ f x) (return e)
    ≡⟨ sym (scanrM-pure-func f e) ⟩⊑  
    return ∘ (scanr f e)
    ⊑∎)

scanrM-head-is-foldrM : ∀ {ℓ} {A B : Type ℓ} (f : A → B → ℙ B) (e : ℙ B) (xs : List A) → (headM =<< scanrM f e xs) ≡ foldrM f e xs 
scanrM-head-is-foldrM f e [] = 
    (headM =<< (wrap <$> e))
    -- Expand the definition of _<$>_
    ≡⟨ refl ⟩
    ((e >>= (λ x → return (wrap x))) >>= headM)

    -- Apply monad associativity
    ≡⟨ >>=-assoc e (λ x → return (wrap x)) headM ⟩
    (e >>= (λ x → return (wrap x) >>= headM))

    -- Evaluate the inner bind using the left identity law
    ≡⟨ cong (λ k → e >>= k) (funExt (λ x → ret-left-id (wrap x) headM)) ⟩
    (e >>= (λ x → headM (wrap x)))

    -- headM (wrap x) = return x
    ≡⟨ refl ⟩
    (e >>= return)

    -- Apply the monad right identity law
    ≡⟨ ret-right-id e ⟩
    e
    ∎
scanrM-head-is-foldrM f e (x ∷ xs) = 
    (headM =<< scanrM f e (x ∷ xs))
    ≡⟨ refl ⟩ 
    (headM =<<
        (scanrM f e xs >>=
        (λ ys → onHead (f x) ys >>= (λ z → return (z ∷ ys)))))
    ≡⟨ manipulate_monad_laws f e x xs ⟩ 
    (onHead (f x) =<< scanrM f e xs)
    ≡⟨ onHead-=<< (f x) (scanrM f e xs) ⟩ 
    f x =<< (headM =<< scanrM f e xs) 
    ≡⟨ cong (λ k → f x =<< k) (scanrM-head-is-foldrM f e xs) ⟩ 
    (f x =<< foldrM f e xs)
    ≡⟨ refl ⟩ 
    foldrM f e (x ∷ xs)
    ∎
    where
    manipulate_monad_laws : ∀ {ℓ} {A B : Type ℓ} (f : A → B → ℙ B) (e : ℙ B) (x : A) (xs : List A) → (headM =<< (scanrM f e xs >>= (λ ys → onHead (f x) ys >>= (λ z → return (z ∷ ys)))))
                ≡ (onHead (f x) =<< scanrM f e xs)
    manipulate_monad_laws f e x xs = 
        ((scanrM f e xs >>= (λ ys → onHead (f x) ys >>= (λ z → return (z ∷ ys)))) >>= headM)
        ≡⟨ >>=-assoc (scanrM f e xs) (λ ys → onHead (f x) ys >>= (λ z → return (z ∷ ys))) headM ⟩
        (scanrM f e xs >>= (λ ys → (onHead (f x) ys >>= (λ z → return (z ∷ ys))) >>= headM))
        ≡⟨ cong (λ k → scanrM f e xs >>= k) (funExt (λ ys → 
            ((onHead (f x) ys >>= (λ z → return (z ∷ ys))) >>= headM)
            ≡⟨ >>=-assoc (onHead (f x) ys) (λ z → return (z ∷ ys)) headM ⟩
            (onHead (f x) ys >>= (λ z → return (z ∷ ys) >>= headM))
            ≡⟨ cong (λ k → onHead (f x) ys >>= k) (funExt (λ z → ret-left-id (z ∷ ys) headM)) ⟩
            (onHead (f x) ys >>= (λ z → return z))
            ≡⟨ ret-right-id (onHead (f x) ys) ⟩
            onHead (f x) ys
            ∎
            )) 
        ⟩
        (onHead (f x) =<< scanrM f e xs)
        ∎

scan-lemma : (f : A → B → ℙ B) (e : ℙ B) → 
              member <=< scanrM f e ⊑ foldrM f e <=< suffix
scan-lemma f e [] = 
    let eq = (
            member =<< scanrM f e []
            ≡⟨ refl ⟩ 
            member =<< (wrap <$> e)
            ≡⟨ refl ⟩ 
            ((e >>= λ x → return [ x ]) >>= member)
            ≡⟨ >>=-assoc e (λ x → return [ x ]) member ⟩ 
            (e >>= λ x → return [ x ] >>= member)
            ≡⟨ cong (λ k → e >>= k) (funExt (λ x → ret-left-id [ x ] member)) ⟩
            (e >>= λ x → member [ x ])
            ≡⟨ refl ⟩ 
            (e >>= λ x → return x ∪ ∅)
            ≡⟨ cong (λ x → e >>= x) (funExt λ x → return-∪-∅ x) ⟩ 
            (e >>= return)
            ≡⟨ ret-right-id e ⟩
            e
            ≡⟨ refl ⟩ 
            foldrM f e []
            ≡⟨ sym (ret-left-id [] (foldrM f e)) ⟩ 
            (foldrM f e =<< return []) 
            ≡⟨ refl ⟩
            foldrM f e =<< suffix []
            ∎)
    in fst (P.⊆-refl-consequence (member =<< scanrM f e []) (foldrM f e =<< suffix []) eq)
scan-lemma f e (x ∷ xs) = reasoning⊆ (
    ⊆begin 
        (member =<< scanrM f e (x ∷ xs))

        -- Expand the defintion of scanrM
        ≡⟨ refl ⟩⊆ 
        (member =<< ((λ ys → (λ z → return (z ∷ ys)) =<< onHead (f x) ys) =<< scanrM f e xs))

        -- Apply monad associativity
        ≡⟨ (>>=-assoc (scanrM f e xs) (λ ys → (λ z → return (z ∷ ys)) =<< onHead (f x) ys) member) ⟩⊆
        (λ ys → member =<< ((λ z → return (z ∷ ys)) =<< onHead (f x) ys)) =<< scanrM f e xs

        -- Use helper-1 to distribute member into the inner return
        ≡⟨ cong (λ k → k =<< scanrM f e xs) (funExt λ ys → sym (helper-1 ys)) ⟩⊆  
        ((λ ys → onHead (f x) ys >>= (λ z → return z ∪ member ys)) =<< scanrM f e xs)

        ⊆⟨ incl helper-⊆-union ⟩
        ((λ ys → onHead (f x) ys ∪ member ys) =<< scanrM f e xs)

        -- Distribute the bind over the union
        ≡⟨ =<<-∪-dist-right (onHead (f x)) member (scanrM f e xs) ⟩⊆
        (onHead (f x) =<< scanrM f e xs) ∪ (member =<< scanrM f e xs)

        -- Un-fuse the head: onHead g =<< m  =  g =<< (headM =<< m)
        ≡⟨ cong (λ w → w ∪ (member =<< scanrM f e xs)) (onHead-=<< (f x) (scanrM f e xs)) ⟩⊆
        (f x =<< (headM =<< scanrM f e xs)) ∪ (member =<< scanrM f e xs)

        -- headM =<< scanrM f e xs = foldrM f e xs 
        ⊆⟨ incl (⊆-∪-monotonic-left 
                (f x =<< (headM =<< scanrM f e xs)) 
                (f x =<< foldrM f e xs) 
                (member =<< scanrM f e xs) 
                (=<<-monotonic-right (f x) (headM =<< scanrM f e xs) (foldrM f e xs)
                    (fst 
                            (P.⊆-refl-consequence 
                                (headM =<< scanrM f e xs) 
                                (foldrM f e xs) 
                                (scanrM-head-is-foldrM f e xs)
                            )
                        )
                )
            ) 
        ⟩
        (f x =<< foldrM f e xs) ∪ (member =<< scanrM f e xs)

        -- Induction
        ⊆⟨ incl (⊆-∪-monotonic-right 
            (member =<< scanrM f e xs) 
            (foldrM f e =<< suffix xs) 
            (f x =<< foldrM f e xs)
            (scan-lemma f e xs)) 
        ⟩ 
        (f x =<< foldrM f e xs) ∪ (foldrM f e =<< suffix xs)

        -- Monad law, definition of foldrM
        ≡⟨ cong (λ k → k ∪ (foldrM f e =<< suffix xs)) (sym (ret-left-id (x ∷ xs) (foldrM f e))) ⟩⊆
        (foldrM f e =<< return (x ∷ xs)) ∪ (foldrM f e =<< suffix xs)

        -- Distributivity between (=<<) and (∪)
        ≡⟨ sym (=<<-∪-dist-left (foldrM f e) (return (x ∷ xs)) (suffix xs)) ⟩⊆
        (foldrM f e =<< (return (x ∷ xs) ∪ suffix xs))
    ⊆∎)
    where
        helper-1 : ∀ ys → (onHead (f x) ys >>= (λ z → return z ∪ member ys)) ≡ ((onHead (f x) ys >>= (λ z → return (z ∷ ys))) >>= member)
        helper-1 ys =  
            (onHead (f x) ys >>= (λ z → member (z ∷ ys)))
            ≡⟨ cong (λ k → onHead (f x) ys >>= k) (funExt λ z → sym (ret-left-id (z ∷ ys) member)) ⟩
            (onHead (f x) ys >>= (λ z → return (z ∷ ys) >>= member))
            ≡⟨ sym (>>=-assoc (onHead (f x) ys) (λ z → return (z ∷ ys)) member) ⟩
            ((onHead (f x) ys >>= (λ z → return (z ∷ ys))) >>= member)
            ∎

        helper-⊆-union : (((λ ys → onHead (f x) ys >>= (λ z → return z ∪ member ys)) =<< scanrM f e xs))
                         ⊆ (((λ ys → onHead (f x) ys ∪ member ys) =<< scanrM f e xs))
        helper-⊆-union = =<<-monotonic-left (scanrM f e xs)
          (λ ys → onHead (f x) ys >>= (λ z → return z ∪ member ys))
          (λ ys → onHead (f x) ys ∪ member ys) 
          lem
          where
            lem : (λ ys → onHead (f x) ys >>= (λ z → return z ∪ member ys)) ⊑
                  (λ ys → onHead (f x) ys ∪ member ys)
            lem ys = reasoning⊆ (
                ⊆begin
                (onHead (f x) ys >>= (λ z → return z ∪ member ys))

                -- Distribute bind `_>>=_` over `_∪_`
                ≡⟨ =<<-∪-dist-right (λ z → return z) (λ _ → member ys) (onHead (f x) ys) ⟩⊆ 
                (return =<< onHead (f x) ys) ∪ ((λ _ → member ys) =<< onHead (f x) ys)

                -- Apply monad Identity
                ≡⟨ cong (λ k → k ∪ ((λ _ → member ys) =<< onHead (f x) ys)) (ret-right-id (onHead (f x) ys)) ⟩⊆
                onHead (f x) ys ∪ ((λ _ → member ys) =<< onHead (f x) ys)

                -- Trivial, the right term is member ys
                ⊆⟨ incl subset-lem ⟩
                onHead (f x) ys ∪ member ys
                ⊆∎)
              where
                -- Proof of the final trivial subset step
                subset-lem : (onHead (f x) ys ∪ ((λ _ → member ys) =<< onHead (f x) ys)) ⊆ (onHead (f x) ys ∪ member ys)
                subset-lem = ∪-⊆-both 
                               (onHead (f x) ys) 
                               ((λ _ → member ys) =<< onHead (f x) ys) 
                               (onHead (f x) ys ∪ member ys)
                             (⊆-∪-left (onHead (f x) ys) (member ys))
                             (λ v p → rec squash₁ (λ {(z , z∈f , v∈mem) → ⊆-∪-right (onHead (f x) ys) (member ys) v v∈mem}) p)        
 
prefix-is-foldrM : {X : Type ℓ} → prefix {X = X} ≡ foldrM {A = X} (pre) (return [])
prefix-is-foldrM = foldrM-fixed-point-properties-eq⇐ pre (return []) prefix (refl , p)
  where
    nil∈prefix : ∀ {X : Type ℓ} (xs : List X) → [] ∈ prefix xs
    nil∈prefix [] = ∣ refl ∣₁
    nil∈prefix (x ∷ xs) = ∣ _⊎_.inl ∣ refl ∣₁ ∣₁
    
    p : ∀ x xs → prefix (x ∷ xs) ≡ (pre x =<< prefix xs)
    p x xs = P.⊆-antisym _ _
      (λ zs → rec squash₁ λ {
        (_⊎_.inl zs≡[]) → ∣ [] , nil∈prefix xs , ∣ _⊎_.inl zs≡[] ∣₁ ∣₁ ;
        (_⊎_.inr m) → rec squash₁ (λ { (ys , ys∈pfx , eq) → ∣ ys , ys∈pfx , ∣ _⊎_.inr eq ∣₁ ∣₁ }) m 
      })
      (λ zs → rec squash₁ λ {
        (ys , ys∈pfx , zs∈prexys) → rec squash₁ (λ {
          (_⊎_.inl zs≡[]) → ∣ _⊎_.inl zs≡[] ∣₁ ;
          (_⊎_.inr zs≡x∷ys) → ∣ _⊎_.inr ∣ ys , ys∈pfx , zs≡x∷ys ∣₁ ∣₁
        }) zs∈prexys
      })

-- subsequences

subseq : List X → ℙ (List X)
subseq [] = return []
subseq (x ∷ xs) = subseq xs ∪ (_∷_ x) <$> subseq xs

subs : X → List X → ℙ (List X)
subs x y = return y ∪ return (x ∷ y)

subseq-is-foldrM : {X : Type ℓ} → subseq {X = X} ≡ foldrM {A = X} subs (return [])
subseq-is-foldrM = foldrM-fixed-point-properties-eq⇐ subs (return []) subseq (refl , p)
  where
    p : ∀ x xs → subseq (x ∷ xs) ≡ (subs x =<< subseq xs)
    p x xs = P.⊆-antisym _ _
      (λ zs → rec squash₁ λ {
        (_⊎_.inl zs∈sxs) → ∣ zs , zs∈sxs , ∣ _⊎_.inl ∣ refl ∣₁ ∣₁ ∣₁ ;
        (_⊎_.inr m) → rec squash₁ (λ { (ys , ys∈sxs , eq) → ∣ ys , ys∈sxs , ∣ _⊎_.inr eq ∣₁ ∣₁ }) m
      })
      (λ zs → rec squash₁ λ {
        (ys , ys∈sxs , zs∈subxys) → rec squash₁ (λ {
          (_⊎_.inl ys≡zs) → ∣ _⊎_.inl (rec (P.∈-isProp (subseq xs) zs) (λ ys≡zs' → subst (λ w → w ∈ subseq xs) ys≡zs' ys∈sxs) ys≡zs) ∣₁ ;
          (_⊎_.inr x∷ys≡zs) → ∣ _⊎_.inr ∣ ys , ys∈sxs , x∷ys≡zs ∣₁ ∣₁
        }) zs∈subxys
      })
