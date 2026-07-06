{-# OPTIONS --without-K --safe #-}

--------------------------------------------------------------------------------
-- Symmetric monoidal coherence solver.
--
-- `solve` proves equality of interpreted free symmetric structural morphisms.
-- `Finite` packages the common case where the atom set is `Fin n`, avoiding
-- caller-facing decidable equality and UIP arguments.
--------------------------------------------------------------------------------

module Categories.Tactic.Monoidal.Symmetric where

open import Level using (Level)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Relation.Binary.Definitions using (DecidableEquality)

open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟Fin_)
open import Relation.Nullary.Decidable using (True; toWitness)

open import Categories.Tactic.Monoidal.Braided
  using (module FreeBraided; module Evaluation; ⇒⇒perm)

module _
  {o ℓ e a : Level}
  {C : Category o ℓ e}
  {M : Monoidal C}
  (S : Symmetric M)
  {Atom : Set a}
  (_≟ₐ_ : DecidableEquality Atom)
  (⟦_⟧ₐ : Atom → Category.Obj C)
  where

  open Symmetric S using (braided)
  open Category C using (_≈_)
  open Evaluation braided ⟦_⟧ₐ using (⟦_⟧ᵇ)
  open FreeBraided Atom

  open import Categories.Tactic.Monoidal.Braided.Soundness braided ⟦_⟧ₐ
    using (solve-realize)
  open import Categories.Tactic.Monoidal.Symmetric.Invariance
    S ⟦_⟧ₐ (Decidable⇒UIP.≡-irrelevant _≟ₐ_)
    using (positions; _≟positions_; realize-positions)

  -- Equal position lists give equal interpretations. On closed free morphisms
  -- both sides compute to closed `List ℕ`, so the `True` witness is inferred.
  solve : ∀ {X Y} (f g : X ⇒ᵇ Y)
    {eq : True (positions (⇒⇒perm f) ≟positions positions (⇒⇒perm g))}
    → ⟦ f ⟧ᵇ ≈ ⟦ g ⟧ᵇ
  solve f g {eq} =
    solve-realize f g (realize-positions (⇒⇒perm f) (⇒⇒perm g) (toWitness eq))

module Finite
  {o ℓ e}
  {C : Category o ℓ e}
  {M : Monoidal C}
  (S : Symmetric M)
  where

  open Category C

  module SolverFor {n} (atom : Fin n → Obj) where
    open import Categories.Tactic.Monoidal.Symmetric.Invariance
      S atom (Decidable⇒UIP.≡-irrelevant _≟Fin_)
      public using (positions; _≟positions_)
    open Evaluation (Symmetric.braided S) atom public using (⟦_⟧ᵇ)
    open FreeBraided (Fin n) public
      renaming
        ( _⇒ᵇ_ to _⇒ᶠ_
        ; _∘ᵇ_ to _∘ᶠ_
        ; _⊗ᵇ_ to _⊗ᶠ_
        ; _⊗_  to _⊗ᵒ_
        ; α⇒   to α⇒ᶠ
        ; α⇐   to α⇐ᶠ
        ; λ⇒   to λ⇒ᶠ
        ; λ⇐   to λ⇐ᶠ
        ; ρ⇒   to ρ⇒ᶠ
        ; ρ⇐   to ρ⇐ᶠ
        ; β    to σᶠ
        )

    solveᶠ : ∀ {X Y} (f g : X ⇒ᶠ Y)
      {eq : True (positions (⇒⇒perm f) ≟positions positions (⇒⇒perm g))}
      → ⟦ f ⟧ᵇ ≈ ⟦ g ⟧ᵇ
    solveᶠ f g {eq} = solve S _≟Fin_ atom f g {eq}
