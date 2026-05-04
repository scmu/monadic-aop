{-# OPTIONS --cubical #-}
module MonadicList where

open import Cubical.Data.List hiding (foldr; rec)
open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)
open import Cubical.Data.Sigma.Base using (_×_) 
open import Cubical.Data.Sum.Base using (_⊎_)
open import Cubical.Data.Empty using (isProp⊥; isProp⊥* ; ⊥* ; elim*; ⊥)
open import Cubical.Data.Unit
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

-- maxlist : List⁺ X → (R : ) → X
-- -- maxlist [ x ]⁺ = x
-- maxlist [ x ]⁺ = {!   !}
-- maxlist (x ∷⁺ xs) = {!   !}

postulate
  impossible-head : ∀ {ℓ} {X : Type ℓ} → X

head : List X → X
head [] = impossible-head
head (x ∷ xs) = x

member : List X → ℙ X
member [] = ∅
member (x ∷ xs) = return x ∪ member xs

-- scan

scanr : (A → B → B) → B → List A → List B
scanr f e [] = [ e ]
scanr f e (x ∷ xs) = f x (head qs) ∷ qs
    where qs = scanr f e xs

scanrM : (A → B → ℙ B) → ℙ B → List A → ℙ (List B)
scanrM f e [] = wrap <$> e
scanrM f e (x ∷ xs) = do
    ys ← scanrM f e xs
    z ← f x (head ys)
    return (z ∷ ys)

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

scanrM-head-is-foldrM : ∀ {ℓ} {A B : Type ℓ} (f : A → B → ℙ B) (e : ℙ B) (xs : List A) → head <$> scanrM f e xs ≡ foldrM f e xs 
scanrM-head-is-foldrM f e [] = 
    (head <$> (wrap <$> e))
    -- Expand the definition of _<$>_
    ≡⟨ refl ⟩
    ((e >>= (λ x → return (wrap x))) >>= (λ ys → return (head ys)))

    -- Apply monad associativity
    ≡⟨ >>=-assoc e (λ x → return (wrap x)) (λ ys → return (head ys)) ⟩
    (e >>= (λ x → return (wrap x) >>= (λ ys → return (head ys))))

    -- Evaluate the inner bind using the left identity law
    ≡⟨ cong (λ k → e >>= k) (funExt (λ x → ret-left-id (wrap x) (λ ys → return (head ys)))) ⟩
    (e >>= (λ x → return (head (wrap x))))

    -- head (wrap x) = x
    ≡⟨ refl ⟩
    (e >>= return)

    -- Apply the monad right identity law
    ≡⟨ ret-right-id e ⟩
    e
    ∎
scanrM-head-is-foldrM f e (x ∷ xs) = 
    (head <$> scanrM f e (x ∷ xs))
    ≡⟨ refl ⟩ 
    (head <$>
        (scanrM f e xs >>=
        (λ ys → f x (head ys) >>= (λ z → return (z ∷ ys)))))
    ≡⟨ manipulate_monad_laws f e x xs ⟩ 
    (f x ∘ head) =<< scanrM f e xs
    ≡⟨ sym (=<<-<$>-fusion (f x) head (scanrM f e xs)) ⟩ 
    f x =<< (head <$> scanrM f e xs) 
    ≡⟨ cong (λ k → f x =<< k) (scanrM-head-is-foldrM f e xs) ⟩ 
    (f x =<< foldrM f e xs)
    ≡⟨ refl ⟩ 
    foldrM f e (x ∷ xs)
    ∎
    where
    manipulate_monad_laws : ∀ {ℓ} {A B : Type ℓ} (f : A → B → ℙ B) (e : ℙ B) (x : A) (xs : List A) → (head <$> (scanrM f e xs >>= (λ ys → f x (head ys) >>= (λ z → return (z ∷ ys)))))
                ≡ ((f x ∘ head) =<< scanrM f e xs)
    manipulate_monad_laws f e x xs = 
        ((scanrM f e xs >>= (λ ys → f x (head ys) >>= (λ z → return (z ∷ ys)))) >>= (λ ws → return (head ws)))
        ≡⟨ >>=-assoc (scanrM f e xs) (λ ys → f x (head ys) >>= (λ z → return (z ∷ ys))) (λ ws → return (head ws)) ⟩
        (scanrM f e xs >>= (λ ys → (f x (head ys) >>= (λ z → return (z ∷ ys))) >>= (λ ws → return (head ws))))
        ≡⟨ cong (λ k → scanrM f e xs >>= k) (funExt (λ ys → 
            ((f x (head ys) >>= (λ z → return (z ∷ ys))) >>= (λ ws → return (head ws)))
            ≡⟨ >>=-assoc (f x (head ys)) (λ z → return (z ∷ ys)) (λ ws → return (head ws)) ⟩
            (f x (head ys) >>= (λ z → return (z ∷ ys) >>= (λ ws → return (head ws))))
            ≡⟨ cong (λ k → f x (head ys) >>= k) (funExt (λ z → ret-left-id (z ∷ ys) (λ ws → return (head ws)))) ⟩
            (f x (head ys) >>= (λ z → return z))
            ≡⟨ ret-right-id (f x (head ys)) ⟩
            f x (head ys)
            ∎
            )) 
        ⟩
        ((f x ∘ head) =<< scanrM f e xs)
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
        (member =<< ((λ ys → (λ z → return (z ∷ ys)) =<< f x (head ys)) =<< scanrM f e xs))

        -- Apply monad associativity
        ≡⟨ (>>=-assoc (scanrM f e xs) (λ ys → (λ z → return (z ∷ ys)) =<< f x (head ys)) member) ⟩⊆
        (λ ys → member =<< ((λ z → return (z ∷ ys)) =<< f x (head ys))) =<< scanrM f e xs

        -- Use helper-1 to distribute member into the inner return
        ≡⟨ cong (λ k → k =<< scanrM f e xs) (funExt λ ys → sym (helper-1 ys)) ⟩⊆  
        ((λ ys → f x (head ys) >>= (λ z → return z ∪ member ys)) =<< scanrM f e xs)

        ⊆⟨ incl helper-⊆-union ⟩
        ((λ ys → f x (head ys) ∪ member ys) =<< scanrM f e xs)

        -- Distribute the bind over the union
        ≡⟨ =<<-∪-dist-right (f x ∘ head) member (scanrM f e xs) ⟩⊆
        ((f x ∘ head) =<< scanrM f e xs) ∪ (member =<< scanrM f e xs)

        -- Un-fuse the map over the head
        ≡⟨ sym (cong (λ w → w ∪ (member =<< scanrM f e xs)) (=<<-<$>-fusion (f x) head (scanrM f e xs))) ⟩⊆
        (f x =<< (head <$> scanrM f e xs)) ∪ (member =<< scanrM f e xs)

        -- head <$> scanR f e xs = foldR f e xs 
        ⊆⟨ incl (⊆-∪-monotonic-left 
                (f x =<< (head <$> scanrM f e xs)) 
                (f x =<< foldrM f e xs) 
                (member =<< scanrM f e xs) 
                (=<<-monotonic-right (f x) (head <$> scanrM f e xs) (foldrM f e xs)
                    (fst 
                            (P.⊆-refl-consequence 
                                (head <$> scanrM f e xs) 
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
        helper-1 : ∀ ys → (f x (head ys) >>= (λ z → return z ∪ member ys)) ≡ ((f x (head ys) >>= (λ z → return (z ∷ ys))) >>= member)
        helper-1 ys =  
            (f x (head ys) >>= (λ z → member (z ∷ ys)))
            ≡⟨ cong (λ k → f x (head ys) >>= k) (funExt λ z → sym (ret-left-id (z ∷ ys) member)) ⟩
            (f x (head ys) >>= (λ z → return (z ∷ ys) >>= member))
            ≡⟨ sym (>>=-assoc (f x (head ys)) (λ z → return (z ∷ ys)) member) ⟩
            ((f x (head ys) >>= (λ z → return (z ∷ ys))) >>= member)
            ∎

        helper-⊆-union : (((λ ys → f x (head ys) >>= (λ z → return z ∪ member ys)) =<< scanrM f e xs))
                         ⊆ (((λ ys → f x (head ys) ∪ member ys) =<< scanrM f e xs))
        helper-⊆-union = =<<-monotonic-left (scanrM f e xs)
          (λ ys → f x (head ys) >>= (λ z → return z ∪ member ys))
          (λ ys → f x (head ys) ∪ member ys) 
          lem
          where
            lem : (λ ys → f x (head ys) >>= (λ z → return z ∪ member ys)) ⊑
                  (λ ys → f x (head ys) ∪ member ys)
            lem ys = reasoning⊆ (
                ⊆begin
                (f x (head ys) >>= (λ z → return z ∪ member ys))

                -- Distribute bind `_>>=_` over `_∪_`
                ≡⟨ =<<-∪-dist-right (λ z → return z) (λ _ → member ys) (f x (head ys)) ⟩⊆ 
                (return =<< f x (head ys)) ∪ ((λ _ → member ys) =<< f x (head ys))

                -- Apply monad Identity
                ≡⟨ cong (λ k → k ∪ ((λ _ → member ys) =<< f x (head ys))) (ret-right-id (f x (head ys))) ⟩⊆
                f x (head ys) ∪ ((λ _ → member ys) =<< f x (head ys))

                -- Trivial, the right term is member ys
                ⊆⟨ incl subset-lem ⟩
                f x (head ys) ∪ member ys
                ⊆∎)
              where
                -- Proof of the final trivial subset step
                subset-lem : (f x (head ys) ∪ ((λ _ → member ys) =<< f x (head ys))) ⊆ (f x (head ys) ∪ member ys)
                subset-lem = ∪-⊆-both 
                               (f x (head ys)) 
                               ((λ _ → member ys) =<< f x (head ys)) 
                               (f x (head ys) ∪ member ys)
                             (⊆-∪-left (f x (head ys)) (member ys))
                             (λ v p → rec squash₁ (λ {(z , z∈f , v∈mem) → ⊆-∪-right (f x (head ys)) (member ys) v v∈mem}) p)        
 
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
