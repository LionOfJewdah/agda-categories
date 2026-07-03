{-# OPTIONS --without-K --safe #-}

--------------------------------------------------------------------------------
-- Core interpretation for monoidal coherence.
--
-- The object-level solver is organized as a monoid homomorphism:
--
--   (List Atom, _++_, [])  --->  (Obj, _⊗₀_, unit, _≅_)
--
-- The source is the free monoid on atoms.  The target is the monoid of objects
-- in a monoidal category, with tensor as multiplication and isomorphism as the
-- equality relation.  Strictification transports an object to the interpretation
-- of its normal form, and `object-coherence` gives the canonical structural
-- isomorphism between any two objects with the same normal form.
--
-- The morphism-level theorem is in `Categories.Tactic.Monoidal.Coherence`.
--------------------------------------------------------------------------------

open import Level using (Level; _⊔_)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)

module Categories.Tactic.Monoidal.Core
  {o ℓ e a : Level}
  {C : Category o ℓ e}
  (M : Monoidal C)
  {Atom : Set a}
  (⟦_⟧ₐ : Atom → Category.Obj C)
  where

open import Data.Product using (_,_)
open import Data.List.Base using (List; []; _∷_; _++_; ++-[]-rawMonoid)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
open import Algebra.Bundles using (Monoid)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)

open import Categories.Morphism C using (_≅_; module ≅)
open import Categories.Category.Monoidal.Utilities M using (_⊗ᵢ_; Obj-⊗-Monoid; module Shorthands)
open import Categories.Morphism.Reasoning C using (module Cancellers)
open import Categories.Category.Monoidal.Reasoning M
  using (⊗-cancel)

open Category C renaming (_⇒_ to _⇒ᶜ_; _∘_ to _∘ᶜ_; id to idᶜ)
open Monoidal M using (_⊗₀_; unit; associator; unitorˡ; unitorʳ)
  renaming (_⊗₁_ to _⊗₁ᶜ_)
open Shorthands
  renaming
    ( α⇒ to α⇒ᶜ ; α⇐ to α⇐ᶜ
    ; λ⇒ to λ⇒ᶜ ; λ⇐ to λ⇐ᶜ
    ; ρ⇒ to ρ⇒ᶜ ; ρ⇐ to ρ⇐ᶜ
    )

-- Free structural expressions for monoidal coherence.  These are the objects
-- and arrows generated only by atoms, the monoidal unit, tensor, associators,
-- and unitors.
module Free {a′ : Level} (Atom : Set a′) where

  infixr 9 _⊗_

  data Ob : Set a′ where
    ‹_› : Atom → Ob
    I   : Ob
    _⊗_ : Ob → Ob → Ob

  infixr 9 _∘_
  infixr 10 _⊗₁_

  data _⇒_ : Ob → Ob → Set a′ where
    idₘ  : ∀ {X}     → X ⇒ X
    _∘_  : ∀ {X Y Z} → Y ⇒ Z → X ⇒ Y → X ⇒ Z
    _⊗₁_ : ∀ {X Y Z W} → X ⇒ Y → Z ⇒ W → (X ⊗ Z) ⇒ (Y ⊗ W)
    α⇒   : ∀ {X Y Z} → ((X ⊗ Y) ⊗ Z) ⇒ (X ⊗ (Y ⊗ Z))
    α⇐   : ∀ {X Y Z} → (X ⊗ (Y ⊗ Z)) ⇒ ((X ⊗ Y) ⊗ Z)
    λ⇒   : ∀ {X} → (I ⊗ X) ⇒ X
    λ⇐   : ∀ {X} → X ⇒ (I ⊗ X)
    ρ⇒   : ∀ {X} → (X ⊗ I) ⇒ X
    ρ⇐   : ∀ {X} → X ⇒ (X ⊗ I)

  invert : ∀ {X Y} → X ⇒ Y → Y ⇒ X
  invert idₘ       = idₘ
  invert (g ∘ f)   = invert f ∘ invert g
  invert (f ⊗₁ g)  = invert f ⊗₁ invert g
  invert α⇒        = α⇐
  invert α⇐        = α⇒
  invert λ⇒        = λ⇐
  invert λ⇐        = λ⇒
  invert ρ⇒        = ρ⇐
  invert ρ⇐        = ρ⇒

  nf : Ob → List Atom
  nf ‹ x ›   = x ∷ []
  nf I       = []
  nf (X ⊗ Y) = nf X ++ nf Y

  ⌜_⌝ : List Atom → Ob
  ⌜ [] ⌝     = I
  ⌜ x ∷ xs ⌝ = ‹ x › ⊗ ⌜ xs ⌝

  nf-⌜⌝ : (w : List Atom) → nf ⌜ w ⌝ ≡ w
  nf-⌜⌝ []       = refl
  nf-⌜⌝ (x ∷ xs) = cong (x ∷_) (nf-⌜⌝ xs)

  module NormalForm where
    -- Normal-form equalities for the structural generators.
    assocₙ : (X Y Z : Ob) → nf ((X ⊗ Y) ⊗ Z) ≡ nf (X ⊗ (Y ⊗ Z))
    assocₙ X Y Z = ++-assoc (nf X) (nf Y) (nf Z)

    assocₙ⁻¹ : (X Y Z : Ob) → nf (X ⊗ (Y ⊗ Z)) ≡ nf ((X ⊗ Y) ⊗ Z)
    assocₙ⁻¹ X Y Z = sym (assocₙ X Y Z)

    unitʳₙ : (X : Ob) → nf (X ⊗ I) ≡ nf X
    unitʳₙ X = ++-identityʳ (nf X)

    unitʳₙ⁻¹ : (X : Ob) → nf X ≡ nf (X ⊗ I)
    unitʳₙ⁻¹ X = sym (unitʳₙ X)

  ⇒⇒nf : ∀ {X Y} → X ⇒ Y → nf X ≡ nf Y
  ⇒⇒nf idₘ              = refl
  ⇒⇒nf (g ∘ f)          = trans (⇒⇒nf f) (⇒⇒nf g)
  ⇒⇒nf (f ⊗₁ g)         = cong₂ _++_ (⇒⇒nf f) (⇒⇒nf g)
  ⇒⇒nf (α⇒ {X} {Y} {Z}) = NormalForm.assocₙ X Y Z
  ⇒⇒nf (α⇐ {X} {Y} {Z}) = NormalForm.assocₙ⁻¹ X Y Z
  ⇒⇒nf λ⇒               = refl
  ⇒⇒nf λ⇐               = refl
  ⇒⇒nf (ρ⇒ {X})         = NormalForm.unitʳₙ X
  ⇒⇒nf (ρ⇐ {X})         = NormalForm.unitʳₙ⁻¹ X

open Free Atom

private
  variable
    X Y Z W : Ob

-- ----------------------------------------------------------------------------
-- §1: The interpretation monoid homomorphism
-- ----------------------------------------------------------------------------
--
-- `eval` sends a normal form (a word in the free monoid) to the canonical
-- right-nested object; it is the unique monoid homomorphism extending
-- `⟦_⟧ₐ`. Its multiplicativity `eval-homo` needs only the associator and left
-- unitor — no pentagon — because a monoid homomorphism records the
-- multiplicativity square, not its coherence.

eval : List Atom → Obj
eval []       = unit
eval (x ∷ xs) = ⟦ x ⟧ₐ ⊗₀ eval xs

eval-homo : (x y : List Atom) → eval (x ++ y) ≅ eval x ⊗₀ eval y
eval-homo []       y = ≅.sym unitorˡ
eval-homo (x ∷ xs) y = ≅.trans (≅.refl ⊗ᵢ eval-homo xs y) (≅.sym associator)

open MonoidMorphisms (++-[]-rawMonoid Atom) (Monoid.rawMonoid Obj-⊗-Monoid)
  using (IsMonoidHomomorphism)

eval-homomorphism : IsMonoidHomomorphism eval
eval-homomorphism = record
  { isMagmaHomomorphism = record
    { isRelHomomorphism = record { cong = λ { refl → ≅.refl } }
    ; homo              = eval-homo
    }
  ; ε-homo = ≅.refl
  }

-- ----------------------------------------------------------------------------
-- §2: Object interpretation and strictification
-- ----------------------------------------------------------------------------
--
-- `⟦_⟧₀` interprets a full object (with bracketing and units); `⟦ ⌜ w ⌝ ⟧₀`
-- coincides definitionally with `eval w`. `strictify` is the canonical iso
-- reassociating any object to (the image of) its normal form.

⟦_⟧₀ : Ob → Obj
⟦ ‹ x › ⟧₀ = ⟦ x ⟧ₐ
⟦ I ⟧₀     = unit
⟦ X ⊗ Y ⟧₀ = ⟦ X ⟧₀ ⊗₀ ⟦ Y ⟧₀

strictify : (X : Ob) → ⟦ X ⟧₀ ≅ eval (nf X)
strictify ‹ x ›   = ≅.sym unitorʳ
strictify I       = ≅.refl
strictify (X ⊗ Y) = ≅.trans (strictify X ⊗ᵢ strictify Y) (≅.sym (eval-homo (nf X) (nf Y)))

-- Object-level coherence: any two objects with the same normal form are
-- canonically isomorphic.  No Mac Lane theorem is needed here; this is the free
-- monoid interpretation transported along `strictify`.
object-coherence : nf X ≡ nf Y → ⟦ X ⟧₀ ≅ ⟦ Y ⟧₀
object-coherence {X} {Y} p =
  ≅.trans (strictify X) (≅.trans (≅.reflexive (cong eval p)) (≅.sym (strictify Y)))

-- ----------------------------------------------------------------------------
-- §3: Morphism interpretation and semantic invertibility
-- ----------------------------------------------------------------------------
--
-- `⟦_⟧₁` is the strictify monoidal functor on arrows; every generator goes to the
-- corresponding structural component. `invert-iso{ˡ,ʳ}` show it sends `invert`
-- to a genuine two-sided inverse, so every free morphism interprets to an iso.

⟦_⟧₁ : X ⇒ Y → ⟦ X ⟧₀ ⇒ᶜ ⟦ Y ⟧₀
⟦ idₘ ⟧₁    = idᶜ
⟦ g ∘ f ⟧₁  = ⟦ g ⟧₁ ∘ᶜ ⟦ f ⟧₁
⟦ f ⊗₁ g ⟧₁ = ⟦ f ⟧₁ ⊗₁ᶜ ⟦ g ⟧₁
⟦ α⇒ ⟧₁     = α⇒ᶜ
⟦ α⇐ ⟧₁     = α⇐ᶜ
⟦ λ⇒ ⟧₁     = λ⇒ᶜ
⟦ λ⇐ ⟧₁     = λ⇐ᶜ
⟦ ρ⇒ ⟧₁     = ρ⇒ᶜ
⟦ ρ⇐ ⟧₁     = ρ⇐ᶜ

invert-isoˡ : (f : X ⇒ Y) → ⟦ invert f ⟧₁ ∘ᶜ ⟦ f ⟧₁ ≈ idᶜ
invert-isoˡ idₘ      = identity²
invert-isoˡ (g ∘ f)  =
  Equiv.trans (Cancellers.cancelInner (invert-isoˡ g)) (invert-isoˡ f)
invert-isoˡ (f ⊗₁ g) = ⊗-cancel (invert-isoˡ f) (invert-isoˡ g)
invert-isoˡ α⇒       = associator.isoˡ
invert-isoˡ α⇐       = associator.isoʳ
invert-isoˡ λ⇒       = unitorˡ.isoˡ
invert-isoˡ λ⇐       = unitorˡ.isoʳ
invert-isoˡ ρ⇒       = unitorʳ.isoˡ
invert-isoˡ ρ⇐       = unitorʳ.isoʳ

invert-isoʳ : (f : X ⇒ Y) → ⟦ f ⟧₁ ∘ᶜ ⟦ invert f ⟧₁ ≈ idᶜ
invert-isoʳ idₘ      = identity²
invert-isoʳ (g ∘ f)  =
  Equiv.trans (Cancellers.cancelInner (invert-isoʳ f)) (invert-isoʳ g)
invert-isoʳ (f ⊗₁ g) = ⊗-cancel (invert-isoʳ f) (invert-isoʳ g)
invert-isoʳ α⇒       = associator.isoʳ
invert-isoʳ α⇐       = associator.isoˡ
invert-isoʳ λ⇒       = unitorˡ.isoʳ
invert-isoʳ λ⇐       = unitorˡ.isoˡ
invert-isoʳ ρ⇒       = unitorʳ.isoʳ
invert-isoʳ ρ⇐       = unitorʳ.isoˡ

-- ----------------------------------------------------------------------------
-- §4: Morphism-level coherence — the reduction to loop-triviality
-- ----------------------------------------------------------------------------
--
-- The morphism statement says that any two parallel structural morphisms
-- interpret equally.  It is equivalent to `Loop-trivial`; this file proves the
-- reduction and exposes `coherence-from-loop` as the primitive used by the full theorem.

open HomReasoning

-- Every structural endomorphism interprets as the identity.
Loop-trivial : Set (a ⊔ e)
Loop-trivial = ∀ {Z} (h : Z ⇒ Z) → ⟦ h ⟧₁ ≈ idᶜ

-- The solver primitive: to show `f` and `g` interpret equally, discharge the
-- single loop `invert g ∘ f`.
coherence-from-loop : {f g : X ⇒ Y} → ⟦ invert g ∘ f ⟧₁ ≈ idᶜ → ⟦ f ⟧₁ ≈ ⟦ g ⟧₁
coherence-from-loop {f = f} {g} loop = begin
  ⟦ f ⟧₁                               ≈˘⟨ identityˡ ⟩
  idᶜ ∘ᶜ ⟦ f ⟧₁                        ≈˘⟨ invert-isoʳ g ⟩∘⟨refl ⟩
  (⟦ g ⟧₁ ∘ᶜ ⟦ invert g ⟧₁) ∘ᶜ ⟦ f ⟧₁   ≈⟨ assoc ⟩
  ⟦ g ⟧₁ ∘ᶜ (⟦ invert g ⟧₁ ∘ᶜ ⟦ f ⟧₁)   ≈⟨ refl⟩∘⟨ loop ⟩
  ⟦ g ⟧₁ ∘ᶜ idᶜ                        ≈⟨ identityʳ ⟩
  ⟦ g ⟧₁                               ∎

-- Loop-triviality delivers full morphism coherence…
coherence-from-loops : Loop-trivial → {f g : X ⇒ Y} → ⟦ f ⟧₁ ≈ ⟦ g ⟧₁
coherence-from-loops loops {f} {g} = coherence-from-loop {f = f} {g = g} (loops (invert g ∘ f))

-- …and conversely (a loop is parallel to `idₘ`), so the two are equivalent and
-- taking loop-triviality as the interface loses no generality.
loops-from-coherence
  : ({Z W : Ob} (f g : Z ⇒ W) → ⟦ f ⟧₁ ≈ ⟦ g ⟧₁) → Loop-trivial
loops-from-coherence coh h = coh h idₘ
