{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

-- Recognizing compact closure.  A monoidal closed category in which every object
-- has an *extranatural* unit `t : unit ⇒ X ⊗₀ [ X , unit ]₀` is left rigid, with
-- `[ X , unit ]₀` the dual of `X` and evaluation the counit; if it is symmetric,
-- it is compact closed.
--
-- Hajgató & Hasegawa, "Traced ∗-autonomous categories are compact closed", TAC
-- 28(7), 2013, Proposition 2.1.  No trace anywhere: this is the elementary half
-- of their theorem.
--
-- Extranaturality is the *enriched* one (their hexagon, p. 208): an equation
-- between two maps out of the hom object `[ X , Y ]₀`, not merely between maps
-- out of the unit.  Its two degenerate instances are the two snakes — `Y := unit`
-- gives `snake₂` on the nose, and `X := unit` gives `snake₁` once transported
-- along `X ≅ [ unit , X ]₀`.
--
-- `t-unit` is their "t_I is invertible", already in the normalized form the
-- construction reduces it to: an arbitrary invertible `t {unit}` is corrected by
-- composing with the scalar `t {unit} ⁻¹ ∘ can`.  Their Remark 2.2 shows the
-- hypothesis cannot be dropped — ωCppo⊥ has an extranatural `t` and is not
-- compact closed.

module Categories.Category.Monoidal.Closed.CompactClosed
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

open import Data.Sum using (inj₁)

open import Categories.Category.Monoidal.Rigid M using (LeftRigid)
open import Categories.Category.Monoidal.CompactClosed M using (CompactClosed)
open import Categories.Category.Monoidal.Symmetric M using (Symmetric)

open Closed Cl using ([_,_]₀)

open Category C
open Monoidal M
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Utilities M
open import Categories.Category.Monoidal.Reassociation M
open import Categories.Category.Monoidal.Closed.Properties Cl
open import Categories.Morphism.Reasoning C
open Shorthands

private
  variable
    X Y : Obj

  -- Two right unitors with an associator between them are two right unitors.
  ρ⇐-collapse : α⇐ ∘ (id {Y} ⊗₁ ρ⇐) ≈ ρ⇐ {Y ⊗₀ unit}
  ρ⇐-collapse = begin
    α⇐ ∘ (id ⊗₁ ρ⇐)  ≈⟨ refl⟩∘⟨ ρ⇐-assoc ⟩
    α⇐ ∘ α⇒ ∘ ρ⇐     ≈⟨ cancelˡ associator.isoˡ ⟩
    ρ⇐               ∎

-- The candidate dual, and the canonical map the unit's own unit must be.

infix 30 _*
_* : Obj → Obj
X * = [ X , unit ]₀

can : unit ⇒ unit ⊗₀ unit *
can = (id ⊗₁ ⌜id⌝) ∘ ρ⇐

module _ (t : ∀ {X} → unit ⇒ X ⊗₀ X *)
    -- Extranaturality: as maps `[ X , Y ]₀ ⇒ Y ⊗₀ X *`, handing a function its
    -- own unit and evaluating agrees with taking the unit of its target and
    -- composing.
    (t-extranatural : ∀ {X Y} →
       (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t {X}) ∘ ρ⇐
     ≈ (id ⊗₁ internal-∘) ∘ α⇒ ∘ (t {Y} ⊗₁ id) ∘ λ⇐)
    (t-unit : t {unit} ≈ can)
    where

  ------------------------------------------------------------------------
  -- `snake₂` is the hexagon at `Y := unit`.  Its left-hand side *is* the snake's
  -- composite; its right-hand side collapses, because composing with the
  -- internal identity is a unitor.

  snake₂ : λ⇒ ∘ (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t {X}) ∘ ρ⇐ ≈ id {X *}
  snake₂ = begin
    λ⇒ ∘ (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ t-extranatural ⟩
    λ⇒ ∘ (id ⊗₁ internal-∘) ∘ α⇒ ∘ (t {unit} ⊗₁ id) ∘ λ⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ (t-unit ⟩⊗⟨refl) ⟩∘⟨refl ⟩
    λ⇒ ∘ (id ⊗₁ internal-∘) ∘ α⇒ ∘ (((id ⊗₁ ⌜id⌝) ∘ ρ⇐) ⊗₁ id) ∘ λ⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₁ˡ ⟩
    λ⇒ ∘ (id ⊗₁ internal-∘) ∘ α⇒ ∘ ((id ⊗₁ ⌜id⌝) ⊗₁ id) ∘ (ρ⇐ ⊗₁ id) ∘ λ⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟩
    λ⇒ ∘ (id ⊗₁ internal-∘) ∘ (id ⊗₁ (⌜id⌝ ⊗₁ id)) ∘ α⇒ ∘ (ρ⇐ ⊗₁ id) ∘ λ⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ triangle-inv′ ⟩
    λ⇒ ∘ (id ⊗₁ internal-∘) ∘ (id ⊗₁ (⌜id⌝ ⊗₁ id)) ∘ (id ⊗₁ λ⇐) ∘ λ⇐
      ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
    λ⇒ ∘ (id ⊗₁ (internal-∘ ∘ (⌜id⌝ ⊗₁ id))) ∘ (id ⊗₁ λ⇐) ∘ λ⇐
      ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ internal-∘-idˡ) ⟩∘⟨refl ⟩
    λ⇒ ∘ (id ⊗₁ λ⇒) ∘ (id ⊗₁ λ⇐) ∘ λ⇐              ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
    λ⇒ ∘ (id ⊗₁ (λ⇒ ∘ λ⇐)) ∘ λ⇐                    ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ unitorˡ.isoʳ) ⟩∘⟨refl ⟩
    λ⇒ ∘ (id ⊗₁ id) ∘ λ⇐                           ≈⟨ refl⟩∘⟨ elimˡ ⊗.identity ⟩
    λ⇒ ∘ λ⇐                                        ≈⟨ unitorˡ.isoʳ ⟩
    id                                             ∎

  ------------------------------------------------------------------------
  -- `snake₁` is the hexagon at `X := unit`, conjugated by `i : X ≅ [ unit , X ]₀`
  -- on the left and by `[ unit , unit ]₀ ≅ unit` on the right.  Both sides of the
  -- hexagon are read off that one instance: the left-hand side becomes `id`, the
  -- right-hand side becomes the snake.

  private
    -- Conjugation: a map `[ unit , X ]₀ ⇒ X ⊗₀ [ unit , unit ]₀`, read as a map
    -- `X ⇒ X` by naming the argument and un-naming the result.
    conj : ([ unit , X ]₀ ⇒ X ⊗₀ unit *) → (X ⇒ X)
    conj h = ρ⇒ ∘ (id ⊗₁ unit-hom⇐) ∘ h ∘ unit-hom⇒

    -- The hexagon's right-hand side: `i⇒` slides through to meet `comp`, and
    -- `comp-i` turns the two of them back into `ev`.
    conj-right : conj ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t {X} ⊗₁ id) ∘ λ⇐)
               ≈ ρ⇒ ∘ (id ⊗₁ eval) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐
    conj-right = begin
      ρ⇒ ∘ (id ⊗₁ unit-hom⇐) ∘ ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐) ∘ unit-hom⇒
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ name-slide ⟩
      ρ⇒ ∘ (id ⊗₁ unit-hom⇐) ∘ (id ⊗₁ (internal-∘ ∘ (id ⊗₁ unit-hom⇒))) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
      ρ⇒ ∘ (id ⊗₁ (unit-hom⇐ ∘ internal-∘ ∘ (id ⊗₁ unit-hom⇒))) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐
        ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ internal-∘-unit-hom) ⟩∘⟨refl ⟩
      ρ⇒ ∘ (id ⊗₁ eval) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐        ∎
      where
        -- The named argument travels from the far right of the composite to the
        -- inside of `comp`, past `t` and the associator.
        name-slide : ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t {X} ⊗₁ id) ∘ λ⇐) ∘ unit-hom⇒
                   ≈ (id ⊗₁ (internal-∘ ∘ (id ⊗₁ unit-hom⇒))) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐
        name-slide = begin
          ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐) ∘ unit-hom⇒       ≈⟨ ⟺ reassoc-tail₅ ⟩
          (id ⊗₁ internal-∘) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐ ∘ unit-hom⇒
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ unitorˡ-commute-to ⟩
          (id ⊗₁ internal-∘) ∘ α⇒ ∘ (t ⊗₁ id) ∘ (id ⊗₁ unit-hom⇒) ∘ λ⇐
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ whisker-comm ⟩
          (id ⊗₁ internal-∘) ∘ α⇒ ∘ ((id ⊗₁ unit-hom⇒) ∘ (t ⊗₁ id)) ∘ λ⇐  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
          (id ⊗₁ internal-∘) ∘ α⇒ ∘ (id ⊗₁ unit-hom⇒) ∘ (t ⊗₁ id) ∘ λ⇐
            ≈⟨ refl⟩∘⟨ pullˡ α⇒-id⊗-commute ⟩
          (id ⊗₁ internal-∘) ∘ ((id ⊗₁ (id ⊗₁ unit-hom⇒)) ∘ α⇒) ∘ (t ⊗₁ id) ∘ λ⇐
            ≈⟨ refl⟩∘⟨ assoc ⟩
          (id ⊗₁ internal-∘) ∘ (id ⊗₁ (id ⊗₁ unit-hom⇒)) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐  ≈⟨ pullˡ merge₂ˡ ⟩
          (id ⊗₁ (internal-∘ ∘ (id ⊗₁ unit-hom⇒))) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐        ∎

    -- The hexagon's left-hand side: with `t {unit}` canonical, everything cancels
    -- and only `i` against its own inverse is left.
    conj-left : conj ((eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t {unit}) ∘ ρ⇐) ≈ id {X}
    conj-left = begin
      ρ⇒ ∘ (id ⊗₁ unit-hom⇐) ∘ ((eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐) ∘ unit-hom⇒
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ unit-fold ⟩∘⟨refl ⟩
      ρ⇒ ∘ (id ⊗₁ unit-hom⇐) ∘ ((eval ⊗₁ id) ∘ (id ⊗₁ ⌜id⌝) ∘ ρ⇐ ∘ ρ⇐) ∘ unit-hom⇒
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (merge₂ʳ ○ (refl⟩⊗⟨ identityˡ)) ⟩∘⟨refl ⟩
      ρ⇒ ∘ (id ⊗₁ unit-hom⇐) ∘ ((eval ⊗₁ ⌜id⌝) ∘ ρ⇐ ∘ ρ⇐) ∘ unit-hom⇒
        ≈⟨ refl⟩∘⟨ pullˡ (pullˡ (merge₂ˡ ○ (refl⟩⊗⟨ unit-hom⇐-⌜id⌝))) ⟩
      ρ⇒ ∘ ((eval ⊗₁ id) ∘ ρ⇐ ∘ ρ⇐) ∘ unit-hom⇒               ≈⟨ refl⟩∘⟨ assoc²βε ⟩
      ρ⇒ ∘ (eval ⊗₁ id) ∘ ρ⇐ ∘ ρ⇐ ∘ unit-hom⇒                 ≈⟨ pullˡ unitorʳ-commute-from ⟩
      (eval ∘ ρ⇒) ∘ ρ⇐ ∘ ρ⇐ ∘ unit-hom⇒                       ≈⟨ assoc ⟩
      eval ∘ ρ⇒ ∘ ρ⇐ ∘ ρ⇐ ∘ unit-hom⇒                         ≈⟨ refl⟩∘⟨ cancelˡ unitorʳ.isoʳ ⟩
      eval ∘ ρ⇐ ∘ unit-hom⇒                                   ≈⟨ sym-assoc ⟩
      (eval ∘ ρ⇐) ∘ unit-hom⇒                                 ≈⟨ unit-hom-isoˡ ⟩
      id                                             ∎
      where
        -- The canonical `t {unit}`, unwound: its `j` floats out to the left and
        -- its unitor merges with the associator.
        unit-fold : (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t {unit}) ∘ ρ⇐
                  ≈ (eval {unit} {X} ⊗₁ id) ∘ (id ⊗₁ ⌜id⌝) ∘ ρ⇐ ∘ ρ⇐
        unit-fold = begin
          (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t) ∘ ρ⇐
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩⊗⟨ t-unit) ⟩∘⟨refl ⟩
          (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ ((id ⊗₁ ⌜id⌝) ∘ ρ⇐)) ∘ ρ⇐
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split₂ˡ ⟩∘⟨refl ⟩
          (eval ⊗₁ id) ∘ α⇐ ∘ ((id ⊗₁ (id ⊗₁ ⌜id⌝)) ∘ (id ⊗₁ ρ⇐)) ∘ ρ⇐
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
          (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ (id ⊗₁ ⌜id⌝)) ∘ (id ⊗₁ ρ⇐) ∘ ρ⇐
            ≈⟨ refl⟩∘⟨ pullˡ (⟺ α⇐-id⊗-commute) ⟩
          (eval ⊗₁ id) ∘ ((id ⊗₁ ⌜id⌝) ∘ α⇐) ∘ (id ⊗₁ ρ⇐) ∘ ρ⇐
            ≈⟨ refl⟩∘⟨ assoc ⟩
          (eval ⊗₁ id) ∘ (id ⊗₁ ⌜id⌝) ∘ α⇐ ∘ (id ⊗₁ ρ⇐) ∘ ρ⇐
            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ ρ⇐-collapse ⟩
          (eval ⊗₁ id) ∘ (id ⊗₁ ⌜id⌝) ∘ ρ⇐ ∘ ρ⇐                ∎

  snake₁ : ρ⇒ ∘ (id ⊗₁ eval) ∘ α⇒ ∘ (t {X} ⊗₁ id) ∘ λ⇐ ≈ id {X}
  snake₁ = begin
    ρ⇒ ∘ (id ⊗₁ eval) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐
      ≈˘⟨ conj-right ⟩
    conj ((id ⊗₁ internal-∘) ∘ α⇒ ∘ (t ⊗₁ id) ∘ λ⇐)
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ t-extranatural ⟩∘⟨refl ⟩
    conj ((eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ t {unit}) ∘ ρ⇐)
      ≈⟨ conj-left ⟩
    id                                     ∎

  ------------------------------------------------------------------------

  leftRigid : LeftRigid
  leftRigid = record
    { _⁻¹    = _*
    ; η      = t
    ; ε      = eval
    ; snake₁ = snake₁
    ; snake₂ = snake₂
    }

  compactClosed : Symmetric → CompactClosed
  compactClosed S = record { symmetric = S ; rigid = inj₁ leftRigid }
