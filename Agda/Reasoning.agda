{-# OPTIONS --cubical #-}

module Reasoning where

open import Cubical.Foundations.Powerset as P using (ℙ; _∈_; _⊆_; ⊆-refl-consequence; ⊆-trans)
open import Cubical.Foundations.Prelude

private
  variable
    ℓ : Level
    X : Type ℓ

data _⊆'_ {ℓ : Level} {X : Type ℓ} (A B : ℙ X) : Type ℓ where
  incl : A ⊆ B → A ⊆' B

⊆'-refl : {ℓ : Level} {X : Type ℓ} {A : ℙ X} → A ⊆' A
⊆'-refl = incl (λ _ z → z)

module ⊆-Reasoning {ℓ} {X : Type ℓ} where
  infix  1 ⊆begin_
  infixr 2 _⊆⟨_⟩_
  infixr 2 _≡⟨_⟩⊆_
  infix  3 _⊆∎

  ⊆begin_ : {x y : ℙ X} → x ⊆' y → x ⊆' y
  ⊆begin x⊆y = x⊆y

  _⊆⟨_⟩_ : (x : ℙ X) {y z : ℙ X} → x ⊆' y → y ⊆' z → x ⊆' z
  _⊆⟨_⟩_ x {y} {z} (incl p) (incl q) = incl (⊆-trans x y z p q)

  _≡⟨_⟩⊆_ : (x : ℙ X) {y z : ℙ X} → x ≡ y → y ⊆' z → x ⊆' z
  _≡⟨_⟩⊆_ x {y} {z} eq (incl q) = incl (⊆-trans x y z (fst (⊆-refl-consequence x y eq)) q)

  _⊆∎ : (x : ℙ X) → x ⊆' x
  x ⊆∎ = ⊆'-refl

  -- Extract the underlying proof when done
  reasoning⊆ : {x y : ℙ X} → x ⊆' y → x ⊆ y
  reasoning⊆ (incl p) = p

open ⊆-Reasoning public using (⊆begin_; _⊆⟨_⟩_; _≡⟨_⟩⊆_; _⊆∎; reasoning⊆)


open import Monad_v2 using (_⊑_; ⊑-trans; ⊑-refl-consequence)

private
  variable
    Y : Type ℓ

data _⊑'_ {ℓ ℓ' : Level} {X : Type ℓ} {Y : Type ℓ'} (A B : X → ℙ Y) : Type (ℓ-max ℓ ℓ') where
  incl⊑ : A ⊑ B → A ⊑' B

⊑'-refl : {ℓ ℓ' : Level} {X : Type ℓ} {Y : Type ℓ'} {A : X → ℙ Y} → A ⊑' A
⊑'-refl = incl⊑ (λ x y z → z)

module ⊑-Reasoning {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} where
  infix  1 ⊑begin_
  infixr 2 _⊑⟨_⟩_
  infixr 2 _≡⟨_⟩⊑_
  infix  3 _⊑∎

  ⊑begin_ : {x y : X → ℙ Y} → x ⊑' y → x ⊑' y
  ⊑begin x⊑y = x⊑y

  _⊑⟨_⟩_ : (x : X → ℙ Y) {y z : X → ℙ Y} → x ⊑' y → y ⊑' z → x ⊑' z
  _⊑⟨_⟩_ x {y} {z} (incl⊑ p) (incl⊑ q) = incl⊑ (⊑-trans {r = x} {s = y} {t = z} p q)

  _≡⟨_⟩⊑_ : (x : X → ℙ Y) {y z : X → ℙ Y} → x ≡ y → y ⊑' z → x ⊑' z
  _≡⟨_⟩⊑_ x {y} {z} eq (incl⊑ q) = incl⊑ (⊑-trans {r = x} {s = y} {t = z} (fst (⊑-refl-consequence x y eq)) q)
  
  _⊑∎ : (x : X → ℙ Y) → x ⊑' x
  x ⊑∎ = ⊑'-refl

  -- Extract the underlying proof when done
  reasoning⊑ : {x y : X → ℙ Y} → x ⊑' y → x ⊑ y
  reasoning⊑ (incl⊑ p) = p

open ⊑-Reasoning public using (⊑begin_; _⊑⟨_⟩_; _≡⟨_⟩⊑_; _⊑∎; reasoning⊑)