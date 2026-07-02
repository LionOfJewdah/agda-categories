{-# OPTIONS --without-K --safe #-}

--------------------------------------------------------------------------------
-- Worked examples for monoidal coherence.
--
--   * `assoc-iso-solved` / `unit-iso-solved` — the OBJECT-level solver hands back
--     the canonical structural isomorphism between two objects with the same
--     normal form.
--   * `reassoc-cancel` — the MORPHISM-level solver primitive `coherence-from-loop`: a
--     two-path equality is discharged by one loop (here an associator iso law).
--   * `triangle-faithful` / `pentagon-faithful` — the interpretation lands
--     exactly on agda-categories' own coherence axioms.
--------------------------------------------------------------------------------

open import Level using (Level)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)

module Categories.Tactic.Monoidal.Examples
  {o ℓ e a : Level}
  {C : Category o ℓ e}
  (M : Monoidal C)
  {Atom : Set a}
  (⟦_⟧ₐ : Atom → Category.Obj C)
  (w x y z : Atom)
  where

open import Relation.Binary.PropositionalEquality using (refl)

open import Categories.Tactic.Monoidal.Core M ⟦_⟧ₐ
open import Categories.Tactic.Monoidal using (solve; solve₀; solveMonoidal)

open import Categories.Morphism C using (_≅_)
open Category C hiding (_⇒_)
open Monoidal M hiding (⊗) renaming (_⊗₁_ to _⊗₁ᶜ_)
open Free Atom renaming (_∘_ to _∘ᶠ_)

-- ----------------------------------------------------------------------------
-- §1: Object-level coherence — the canonical isomorphism, for free
-- ----------------------------------------------------------------------------
--
-- `(‹w› ⊗ ‹x›) ⊗ ‹y›` and `‹w› ⊗ (‹x› ⊗ ‹y›)` share the normal form
-- `w ∷ x ∷ y ∷ []`, so `object-coherence refl` produces the canonical iso between
-- their interpretations. No manual associator wrangling.
assoc-iso : ⟦ (‹ w › ⊗ ‹ x ›) ⊗ ‹ y › ⟧₀ ≅ ⟦ ‹ w › ⊗ (‹ x › ⊗ ‹ y ›) ⟧₀
assoc-iso = object-coherence {X = (‹ w › ⊗ ‹ x ›) ⊗ ‹ y ›}
                         {Y = ‹ w › ⊗ (‹ x › ⊗ ‹ y ›)} refl

assoc-iso-solved : ⟦ (‹ w › ⊗ ‹ x ›) ⊗ ‹ y › ⟧₀ ≅ ⟦ ‹ w › ⊗ (‹ x › ⊗ ‹ y ›) ⟧₀
assoc-iso-solved = solve₀ M ⟦_⟧ₐ

-- Units are erased by the normal form too: `(I ⊗ ‹w›) ⊗ (‹x› ⊗ I)` and
-- `‹w› ⊗ ‹x›` both normalise to `w ∷ x ∷ []`.
unit-iso : ⟦ (I ⊗ ‹ w ›) ⊗ (‹ x › ⊗ I) ⟧₀ ≅ ⟦ ‹ w › ⊗ ‹ x › ⟧₀
unit-iso = object-coherence {X = (I ⊗ ‹ w ›) ⊗ (‹ x › ⊗ I)}
                        {Y = ‹ w › ⊗ ‹ x ›} refl

unit-iso-solved : ⟦ (I ⊗ ‹ w ›) ⊗ (‹ x › ⊗ I) ⟧₀ ≅ ⟦ ‹ w › ⊗ ‹ x › ⟧₀
unit-iso-solved = solve₀ M ⟦_⟧ₐ

-- ----------------------------------------------------------------------------
-- §2: Morphism-level — discharge an equality by one loop
-- ----------------------------------------------------------------------------
--
-- `α⇐ ∘ α⇒` and the identity are two structural paths on `(‹w›⊗‹x›)⊗‹y›`.
-- `coherence-from-loop` reduces "they agree" to "their loop is trivial", and the loop here
-- is exactly the associator's left iso law.
reassoc-cancel
  : ⟦ α⇐ ∘ᶠ α⇒ {‹ w ›} {‹ x ›} {‹ y ›} ⟧₁
    ≈ ⟦ idₘ {(‹ w › ⊗ ‹ x ›) ⊗ ‹ y ›} ⟧₁
reassoc-cancel =
  coherence-from-loop {f = α⇐ ∘ᶠ α⇒ {‹ w ›} {‹ x ›} {‹ y ›}} {g = idₘ}
    (Equiv.trans identityˡ associator.isoˡ)

-- ----------------------------------------------------------------------------
-- §3: Faithfulness — the interpretation reproduces the coherence axioms
-- ----------------------------------------------------------------------------

triangle-faithful
  : ⟦ (idₘ ⊗₁ λ⇒) ∘ᶠ α⇒ {‹ w ›} {I} {‹ x ›} ⟧₁
    ≈ ⟦ ρ⇒ {‹ w ›} ⊗₁ idₘ {‹ x ›} ⟧₁
triangle-faithful = triangle

pentagon-faithful
  : ⟦ (idₘ ⊗₁ α⇒) ∘ᶠ
      (α⇒ ∘ᶠ (α⇒ {‹ w ›} {‹ x ›} {‹ y ›} ⊗₁ idₘ {‹ z ›})) ⟧₁
    ≈ ⟦ α⇒ ∘ᶠ α⇒ {‹ w › ⊗ ‹ x ›} {‹ y ›} {‹ z ›} ⟧₁
pentagon-faithful = pentagon

-- The reflection macro invokes the coherence theorem for goals already
-- expressed as interpreted structural paths.
private
  reassoc-cancel-goal : Set e
  reassoc-cancel-goal =
    ⟦ α⇐ ∘ᶠ α⇒ {‹ w ›} {‹ x ›} {‹ y ›} ⟧₁
    ≈ ⟦ idₘ {(‹ w › ⊗ ‹ x ›) ⊗ ‹ y ›} ⟧₁

reassoc-cancel-solved
  : ⟦ α⇐ ∘ᶠ α⇒ {‹ w ›} {‹ x ›} {‹ y ›} ⟧₁
    ≈ ⟦ idₘ {(‹ w › ⊗ ‹ x ›) ⊗ ‹ y ›} ⟧₁
reassoc-cancel-solved = solveMonoidal M ⟦_⟧ₐ

reassoc-cancel-solved-via-alias : reassoc-cancel-goal
reassoc-cancel-solved-via-alias = solve M ⟦_⟧ₐ
