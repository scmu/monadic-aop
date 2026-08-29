{-# OPTIONS --cubical --guardedness #-}
module Shrink where

open import Cubical.Foundations.Prelude 
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma.Base using (_×_) 
open import Cubical.Functions.Logic hiding (_⊓_; _⊔_)
open import Cubical.HITs.PropositionalTruncation as PT  hiding (map)
import Cubical.HITs.PropositionalTruncation.Monad as TruncMonad
open import Cubical.Data.Sum.Base using (_⊎_)
open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_)

open import Sets
open import Monad_v2

private
  variable
    ℓ : Level

_↾_ : {X Y : Type ℓ} → (s : X → ℙ Y) → (R : Y → ℙ Y) → X → ℙ Y
s ↾ r = s ⊓ (r / (s °))

↾-universal-⇒₁ : {X Y : Type ℓ} {t s : X → ℙ Y} {r : Y → ℙ Y}
                 → t ⊑ s ↾ r 
                 → t ⊑ s
↾-universal-⇒₁ {t = t} {s} {r} t⊑s↾r = fst (⊓-universal-⇒ {r = t} {s = s} {t = r / (s °)} t⊑s↾r) -- use property of ⊓

↾-universal-⇒₂ : {X Y : Type ℓ} {t s : X → ℙ Y} {r : Y → ℙ Y}
                 → t ⊑ s ↾ r 
                 → t <=< (s °) ⊑ r 
↾-universal-⇒₂ {t = t} {s} {r} t⊑s↾r = /-universal-⇐ t (s °) r (snd (⊓-universal-⇒ {r = t} {s = s} {t = r / (s °)} t⊑s↾r))

↾-universal-⇒ : {X Y : Type ℓ} {t s : X → ℙ Y} {r : Y → ℙ Y}
                 → t ⊑ s ↾ r 
                 → (t ⊑ s) × (t <=< (s °) ⊑ r)
↾-universal-⇒ {t = t} {s} {r} t⊑s↾r = 
    ↾-universal-⇒₁ {t = t} {s} {r} t⊑s↾r , 
    ↾-universal-⇒₂ {t = t} {s} {r} t⊑s↾r

↾-universal-⇐ : {X Y : Type ℓ} {t s : X → ℙ Y} {r : Y → ℙ Y}
                 → (t ⊑ s) × (t <=< (s °) ⊑ r)
                 → t ⊑ s ↾ r 
↾-universal-⇐ {t = t} {s} {r} (t⊑s , t<=<s°⊑r) = ⊓-universal-⇐ {r = t} {s = s} {t = r / (s °)} (t⊑s , /-universal-⇒ t (s °) r t<=<s°⊑r)
