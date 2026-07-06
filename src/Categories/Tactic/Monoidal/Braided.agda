{-# OPTIONS --without-K --safe #-}

module Categories.Tactic.Monoidal.Braided where

open import Level using (Level)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; ↭-refl; ↭-reflexive; ↭-sym; refl; trans; prep; swap)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (++⁺)
open import Relation.Binary.PropositionalEquality using (sym)

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Braided using (Braided)

open import Categories.Tactic.Monoidal.Free using (module Free)

-- Syntax of the free braided monoidal category

module FreeBraided {a : Level} (Atom : Set a) where

  open Free Atom public using (Ob; ‹_›; I; _⊗_; nf; ⌜_⌝)

  infixr 9 _∘ᵇ_
  infixr 10 _⊗ᵇ_

  data _⇒ᵇ_ : Ob → Ob → Set a where
    idₘ  : ∀ {X}     → X ⇒ᵇ X
    _∘ᵇ_ : ∀ {X Y Z} → Y ⇒ᵇ Z → X ⇒ᵇ Y → X ⇒ᵇ Z
    _⊗ᵇ_ : ∀ {X Y Z W} → X ⇒ᵇ Y → Z ⇒ᵇ W → (X ⊗ Z) ⇒ᵇ (Y ⊗ W)
    α⇒   : ∀ {X Y Z} → ((X ⊗ Y) ⊗ Z) ⇒ᵇ (X ⊗ (Y ⊗ Z))
    α⇐   : ∀ {X Y Z} → (X ⊗ (Y ⊗ Z)) ⇒ᵇ ((X ⊗ Y) ⊗ Z)
    λ⇒   : ∀ {X} → (I ⊗ X) ⇒ᵇ X
    λ⇐   : ∀ {X} → X ⇒ᵇ (I ⊗ X)
    ρ⇒   : ∀ {X} → (X ⊗ I) ⇒ᵇ X
    ρ⇐   : ∀ {X} → X ⇒ᵇ (X ⊗ I)
    β    : ∀ {X Y} → (X ⊗ Y) ⇒ᵇ (Y ⊗ X)

  invert : ∀ {X Y} → X ⇒ᵇ Y → Y ⇒ᵇ X
  invert idₘ       = idₘ
  invert (g ∘ᵇ f)  = invert f ∘ᵇ invert g
  invert (f ⊗ᵇ g)  = invert f ⊗ᵇ invert g
  invert α⇒        = α⇐
  invert α⇐        = α⇒
  invert λ⇒        = λ⇐
  invert λ⇐        = λ⇒
  invert ρ⇒        = ρ⇐
  invert ρ⇐        = ρ⇒
  invert β         = β

module _ {a : Level} {Atom : Set a} where

  open FreeBraided Atom

  shift : (v : Atom) (xs ys : List Atom) → (xs ++ v ∷ ys) ↭ (v ∷ (xs ++ ys))
  shift v []       ys = refl
  shift v (x ∷ xs) ys = trans (prep x (shift v xs ys)) (swap x v refl)

  ++-swap : (xs ys : List Atom) → (xs ++ ys) ↭ (ys ++ xs)
  ++-swap []       ys = ↭-sym (↭-reflexive (++-identityʳ ys))
  ++-swap (x ∷ xs) ys = trans (prep x (++-swap xs ys)) (↭-sym (shift x ys xs))

  ⇒⇒perm : ∀ {X Y} → X ⇒ᵇ Y → nf X ↭ nf Y
  ⇒⇒perm idₘ              = ↭-refl
  ⇒⇒perm (g ∘ᵇ f)         = trans (⇒⇒perm f) (⇒⇒perm g)
  ⇒⇒perm (f ⊗ᵇ g)         = ++⁺ (⇒⇒perm f) (⇒⇒perm g)
  ⇒⇒perm (α⇒ {X} {Y} {Z}) = ↭-reflexive (++-assoc (nf X) (nf Y) (nf Z))
  ⇒⇒perm (α⇐ {X} {Y} {Z}) = ↭-reflexive (sym (++-assoc (nf X) (nf Y) (nf Z)))
  ⇒⇒perm λ⇒               = ↭-refl
  ⇒⇒perm λ⇐               = ↭-refl
  ⇒⇒perm (ρ⇒ {X})         = ↭-reflexive (++-identityʳ (nf X))
  ⇒⇒perm (ρ⇐ {X})         = ↭-reflexive (sym (++-identityʳ (nf X)))
  ⇒⇒perm (β {X} {Y})      = ++-swap (nf X) (nf Y)

module Evaluation
  {o ℓ e a : Level}
  {𝒞 : Category o ℓ e}
  {V : Monoidal 𝒞}
  (B : Braided V)
  {Atom : Set a}
  (⟦_⟧ₐ : Atom → Category.Obj 𝒞)
  where

  open import Data.Product using (_,_)
  open import Categories.Tactic.Monoidal.Core V ⟦_⟧ₐ using (⟦_⟧₀)

  open Category 𝒞 renaming (_⇒_ to _⇒ᶜ_; _∘_ to _∘ᶜ_; id to idᶜ)
  open Monoidal V using (_⊗₀_) renaming (_⊗₁_ to _⊗₁ᶜ_)
  open Braided B using (braiding)
  open import Categories.Category.Monoidal.Utilities V using (module Shorthands)
  open Shorthands
  open FreeBraided Atom renaming
    ( α⇒ to α⇒ᵇ; α⇐ to α⇐ᵇ; λ⇒ to λ⇒ᵇ
    ; λ⇐ to λ⇐ᵇ; ρ⇒ to ρ⇒ᵇ; ρ⇐ to ρ⇐ᵇ )

  private
    variable
      X Y : Ob

  σ⇒ : ∀ {P Q} → (P ⊗₀ Q) ⇒ᶜ (Q ⊗₀ P)
  σ⇒ {P} {Q} = braiding.⇒.η (P , Q)

  ⟦_⟧ᵇ : X ⇒ᵇ Y → ⟦ X ⟧₀ ⇒ᶜ ⟦ Y ⟧₀
  ⟦ idₘ ⟧ᵇ     = idᶜ
  ⟦ g ∘ᵇ f ⟧ᵇ  = ⟦ g ⟧ᵇ ∘ᶜ ⟦ f ⟧ᵇ
  ⟦ f ⊗ᵇ g ⟧ᵇ  = ⟦ f ⟧ᵇ ⊗₁ᶜ ⟦ g ⟧ᵇ
  ⟦ α⇒ᵇ ⟧ᵇ     = α⇒
  ⟦ α⇐ᵇ ⟧ᵇ     = α⇐
  ⟦ λ⇒ᵇ ⟧ᵇ     = λ⇒
  ⟦ λ⇐ᵇ ⟧ᵇ     = λ⇐
  ⟦ ρ⇒ᵇ ⟧ᵇ     = ρ⇒
  ⟦ ρ⇐ᵇ ⟧ᵇ     = ρ⇐
  ⟦ β ⟧ᵇ       = σ⇒
