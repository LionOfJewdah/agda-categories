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
open import Data.List.Base using (List; []; _∷_; _++_; foldr; ++-[]-rawMonoid)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)
open import Algebra.Bundles using (Monoid)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)

open import Categories.Tactic.Monoidal.Free public
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
eval = foldr (λ x xs → ⟦ x ⟧ₐ ⊗₀ xs) unit

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
