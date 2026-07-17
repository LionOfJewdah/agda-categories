{-# OPTIONS --without-K --safe #-}

-- A compact closed category has *exactly one* trace: any operation satisfying the
-- JSV axioms agrees with the canonical trace built from the cups and caps
-- (`Trace.Definition`).  With `Trace.Construction`, the trace is therefore unique.
--
-- Hasegawa, "On traced monoidal closed categories", MSCS 19(2), 2009, Appendix B
-- (Proposition B.1), which proves it for tortile categories; a compact closed
-- category is a tortile one whose twist is the identity.  The proof there is
-- graphical, in four steps; this is its algebraic form.
--
-- `f` disappears in one step: `f` is recovered from its name (`ev-name`, a snake),
-- so `Tr f ≈ Tr ev ∘ name f` by tightening — and `trace f ≈ capᵗʳ ∘ name f` holds by
-- definition.  Uniqueness is therefore `Tr ev ≈ capᵗʳ`, a statement with no `f` in
-- it.  That is `ev-swap` (`ev` is `capᵗʳ` with the two `X` wires crossed — the
-- crossing in Hasegawa's picture) together with `Tr swap ≈ id`, which is
-- superposing plus yanking.
--
-- Only four axioms are used: the two tightenings, superposing and yanking.  Sliding
-- and the two vanishings never appear.

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Monoidal.Rigid using (LeftRigid)
open import Categories.Category.Monoidal.CompactClosed using (CompactClosed)
open import Categories.Category.Monoidal.Traced using (Traced)
open import Data.Product using (_,_)

module Categories.Category.Monoidal.CompactClosed.Trace.Uniqueness
    {o ℓ e} {𝒞 : Category o ℓ e} (M : Monoidal 𝒞) (K : CompactClosed M) where

open Category 𝒞
open CompactClosed K
open LeftRigid leftRigid

open Symmetric symmetric using (braided; commutative; hexagon₁)

open import Categories.Category.Monoidal.Reasoning M
open import Categories.Morphism.Reasoning 𝒞
open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Braided.Properties braided
  renaming (module Shorthands to BraidShorthands)
open import Categories.Category.Monoidal.Reassociation M
open import Categories.Category.Monoidal.CompactClosed.Trace.Definition M K
  using (capᵗʳ; cupᵗʳ; capʳ; capᵗʳ-fold; trace)
open import Categories.Category.Monoidal.Traced.PreTrace M using (PreTrace)
open import Categories.Category.Monoidal.Utilities M as MonUtil
open MonUtil.Shorthands
open BraidShorthands using (σ⇒; σ⇒-comm)

private
  variable
    A B C W X Y Z : Obj

------------------------------------------------------------------------------
-- A wire, beside a box.
--
-- Every map below acts on the last two wires of `(Z ⊗₀ X) ⊗₀ Y` while the first
-- one merely watches.  `│⟦ h ⟧` is that picture — the spectator wire `│`, and
-- beside it the box `h`: re-bracket, run `h`, re-bracket back.
--
--         Z         X′  Y′
--         │          │  │
--         │        ┌─┴──┴─┐
--         │        │  h   │
--         │        └─┬──┬─┘
--         │          │  │
--         Z          X  Y
--
-- It is a functor (`⟦⟧-∘`, `⟦⟧-id`).  That, plus what it does to an associator
-- (`⟦⟧-α⇒`, `⟦⟧-α⇐`) and to a whiskered map (`⟦⟧-⊗id`, `⟦⟧-id⊗`), is everything
-- we use about it: no associator is pushed around by hand below.

│⟦_⟧ : ∀ {Z X Y A B} → X ⊗₀ Y ⇒ A ⊗₀ B → (Z ⊗₀ X) ⊗₀ Y ⇒ (Z ⊗₀ A) ⊗₀ B
│⟦ h ⟧ = α⇐ ∘ (id ⊗₁ h) ∘ α⇒

private
  -- The spectator is the one wire the equations cannot infer, so each statement
  -- names it once, in prefix form; every other wire follows from the equation.

  ⟦⟧-resp-≈ : {h k : X ⊗₀ Y ⇒ A ⊗₀ B} → h ≈ k → │⟦_⟧ {Z} h ≈ │⟦ k ⟧
  ⟦⟧-resp-≈ h≈k = refl⟩∘⟨ (refl⟩⊗⟨ h≈k) ⟩∘⟨refl

  -- Functoriality.  The re-bracketing in the middle cancels.
  ⟦⟧-∘ : {h : A ⊗₀ B ⇒ C ⊗₀ W} {k : X ⊗₀ Y ⇒ A ⊗₀ B} →
    │⟦_⟧ {Z} h ∘ │⟦ k ⟧ ≈ │⟦ h ∘ k ⟧
  ⟦⟧-∘ {h = h} {k = k} = begin
    (α⇐ ∘ (id ⊗₁ h) ∘ α⇒) ∘ (α⇐ ∘ (id ⊗₁ k) ∘ α⇒)  ≈⟨ assoc²βε ⟩
    α⇐ ∘ (id ⊗₁ h) ∘ α⇒ ∘ α⇐ ∘ (id ⊗₁ k) ∘ α⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cancelˡ associator.isoʳ ⟩
    α⇐ ∘ (id ⊗₁ h) ∘ (id ⊗₁ k) ∘ α⇒                ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
    α⇐ ∘ (id ⊗₁ (h ∘ k)) ∘ α⇒                      ∎

  ⟦⟧-id : │⟦_⟧ {Z} (id {X ⊗₀ Y}) ≈ id
  ⟦⟧-id = begin
    α⇐ ∘ (id ⊗₁ id) ∘ α⇒  ≈⟨ refl⟩∘⟨ elimˡ ⊗.identity ⟩
    α⇐ ∘ α⇒               ≈⟨ associator.isoˡ ⟩
    id                    ∎

  -- A box touching only one of the two wires slides out of the brackets.
  ⟦⟧-⊗id : {f : X ⇒ A} → │⟦_⟧ {Z} (f ⊗₁ id {Y}) ≈ (id ⊗₁ f) ⊗₁ id
  ⟦⟧-⊗id {f = f} = begin
    α⇐ ∘ (id ⊗₁ (f ⊗₁ id)) ∘ α⇒    ≈⟨ pullˡ assoc-commute-to ⟩
    (((id ⊗₁ f) ⊗₁ id) ∘ α⇐) ∘ α⇒  ≈⟨ cancelʳ associator.isoˡ ⟩
    (id ⊗₁ f) ⊗₁ id                ∎

  ⟦⟧-id⊗ : {f : Y ⇒ B} → │⟦_⟧ {Z} (id {X} ⊗₁ f) ≈ id ⊗₁ f
  ⟦⟧-id⊗ {f = f} = begin
    α⇐ ∘ (id ⊗₁ (id ⊗₁ f)) ∘ α⇒  ≈⟨ pullˡ (⟺ α⇐-id⊗-commute) ⟩
    ((id ⊗₁ f) ∘ α⇐) ∘ α⇒        ≈⟨ cancelʳ associator.isoˡ ⟩
    id ⊗₁ f                      ∎

  -- An associator in the box is an associator outside it: the two pentagon
  -- instances, already proved in `Reassociation`.
  ⟦⟧-α⇐ : │⟦_⟧ {Z} (α⇐ {X} {Y} {W}) ≈ (α⇒ ⊗₁ id) ∘ α⇐
  ⟦⟧-α⇐ = begin
    α⇐ ∘ (id ⊗₁ α⇐) ∘ α⇒       ≈⟨ refl⟩∘⟨ assoc-to-coherence ⟩
    α⇐ ∘ α⇒ ∘ (α⇒ ⊗₁ id) ∘ α⇐  ≈⟨ cancelˡ associator.isoˡ ⟩
    (α⇒ ⊗₁ id) ∘ α⇐            ∎

  ⟦⟧-α⇒ : │⟦_⟧ {Z} (α⇒ {X} {Y} {W}) ≈ α⇒ ∘ (α⇐ ⊗₁ id)
  ⟦⟧-α⇒ = ⟺ assoc-from-coherence

------------------------------------------------------------------------------
-- The crossing.

-- Braid the last two wires past the spectator.  `φ` is an involution, because the
-- braiding is one and `│⟦_⟧` is a functor.
φ : ∀ {Z X Y} → (Z ⊗₀ X) ⊗₀ Y ⇒ (Z ⊗₀ Y) ⊗₀ X
φ = │⟦ σ⇒ ⟧

φ-inv : φ ∘ φ ≈ id {(Z ⊗₀ X) ⊗₀ Y}
φ-inv = begin
  │⟦ σ⇒ ⟧ ∘ │⟦ σ⇒ ⟧  ≈⟨ ⟦⟧-∘ ⟩
  │⟦ σ⇒ ∘ σ⇒ ⟧       ≈⟨ ⟦⟧-resp-≈ commutative ⟩
  │⟦ id ⟧            ≈⟨ ⟦⟧-id ⟩
  id                 ∎

-- `φ` is natural in the wire the braiding drags along.
φ-natural : {c : X ⇒ Y} → φ {Z} {B} ∘ (id ⊗₁ c) ≈ ((id ⊗₁ c) ⊗₁ id) ∘ φ
φ-natural {c = c} = begin
  φ ∘ (id ⊗₁ c)           ≈˘⟨ refl⟩∘⟨ ⟦⟧-id⊗ ⟩
  │⟦ σ⇒ ⟧ ∘ │⟦ id ⊗₁ c ⟧  ≈⟨ ⟦⟧-∘ ⟩
  │⟦ σ⇒ ∘ (id ⊗₁ c) ⟧     ≈⟨ ⟦⟧-resp-≈ σ⇒-comm ⟩
  │⟦ (c ⊗₁ id) ∘ σ⇒ ⟧     ≈˘⟨ ⟦⟧-∘ ⟩
  │⟦ c ⊗₁ id ⟧ ∘ │⟦ σ⇒ ⟧  ≈⟨ ⟦⟧-⊗id ⟩∘⟨refl ⟩
  ((id ⊗₁ c) ⊗₁ id) ∘ φ   ∎

private
  -- The hexagon, solved for the braiding of `X` past a *pair* of wires.
  hexagonᵖ : σ⇒ {X} {Y ⊗₀ B} ≈ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐
  hexagonᵖ = begin
    σ⇒                                        ≈˘⟨ cancelʳ associator.isoʳ ⟩
    (σ⇒ ∘ α⇒) ∘ α⇐                            ≈˘⟨ cancelˡ associator.isoˡ ⟩∘⟨refl ⟩
    (α⇐ ∘ α⇒ ∘ σ⇒ ∘ α⇒) ∘ α⇐                  ≈˘⟨ (refl⟩∘⟨ hexagon₁) ⟩∘⟨refl ⟩
    (α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)) ∘ α⇐  ≈⟨ assoc ⟩
    α⇐ ∘ ((id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)) ∘ α⇐  ≈⟨ refl⟩∘⟨ assoc²βε ⟩
    α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐    ∎

  -- The same, moved inside the brackets: five boxes in a row, each of which the
  -- lemmas above already know how to open.
  │-hexagon : │⟦_⟧ {Z} (σ⇒ {X} {Y ⊗₀ B})
            ≈ │⟦ α⇐ ⟧ ∘ │⟦ id ⊗₁ σ⇒ ⟧ ∘ │⟦ α⇒ ⟧ ∘ │⟦ σ⇒ ⊗₁ id ⟧ ∘ │⟦ α⇐ ⟧
  │-hexagon = begin
    │⟦ σ⇒ ⟧
      ≈⟨ ⟦⟧-resp-≈ hexagonᵖ ⟩
    │⟦ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐ ⟧
      ≈˘⟨ ⟦⟧-∘ ⟩
    │⟦ α⇐ ⟧ ∘ │⟦ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐ ⟧
      ≈˘⟨ refl⟩∘⟨ ⟦⟧-∘ ⟩
    │⟦ α⇐ ⟧ ∘ │⟦ id ⊗₁ σ⇒ ⟧ ∘ │⟦ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐ ⟧
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟦⟧-∘ ⟩
    │⟦ α⇐ ⟧ ∘ │⟦ id ⊗₁ σ⇒ ⟧ ∘ │⟦ α⇒ ⟧ ∘ │⟦ (σ⇒ ⊗₁ id) ∘ α⇐ ⟧
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟦⟧-∘ ⟩
    │⟦ α⇐ ⟧ ∘ │⟦ id ⊗₁ σ⇒ ⟧ ∘ │⟦ α⇒ ⟧ ∘ │⟦ σ⇒ ⊗₁ id ⟧ ∘ │⟦ α⇐ ⟧  ∎

-- Braiding `X` past `Y ⊗₀ B` in one go is braiding it past `Y`, then past `B`:
-- the hexagon, with the spectator watching.  This is the crossing in Hasegawa's
-- picture, and the only place the hexagon is used.
φ-fuse : ∀ {Z X Y B} → φ ∘ α⇒ {Z ⊗₀ X} {Y} {B} ≈ (α⇒ ⊗₁ id) ∘ φ ∘ (φ ⊗₁ id)
φ-fuse = begin
  │⟦ σ⇒ ⟧ ∘ α⇒
    ≈⟨ │-hexagon ⟩∘⟨refl ⟩
  (│⟦ α⇐ ⟧ ∘ │⟦ id ⊗₁ σ⇒ ⟧ ∘ │⟦ α⇒ ⟧ ∘ │⟦ σ⇒ ⊗₁ id ⟧ ∘ │⟦ α⇐ ⟧) ∘ α⇒
    ≈⟨ ⟺ reassoc-tail₆ ⟩
  │⟦ α⇐ ⟧ ∘ │⟦ id ⊗₁ σ⇒ ⟧ ∘ │⟦ α⇒ ⟧ ∘ │⟦ σ⇒ ⊗₁ id ⟧ ∘ │⟦ α⇐ ⟧ ∘ α⇒
    ≈⟨ ⟦⟧-α⇐ ⟩∘⟨ ⟦⟧-id⊗ ⟩∘⟨ ⟦⟧-α⇒ ⟩∘⟨ ⟦⟧-⊗id ⟩∘⟨ tail-cancel ⟩
  ((α⇒ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ σ⇒) ∘ (α⇒ ∘ (α⇐ ⊗₁ id)) ∘ ((id ⊗₁ σ⇒) ⊗₁ id) ∘ (α⇒ ⊗₁ id)
    ≈⟨ assoc ⟩
  (α⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ (α⇒ ∘ (α⇐ ⊗₁ id)) ∘ ((id ⊗₁ σ⇒) ⊗₁ id) ∘ (α⇒ ⊗₁ id)
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
  (α⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (α⇐ ⊗₁ id) ∘ ((id ⊗₁ σ⇒) ⊗₁ id) ∘ (α⇒ ⊗₁ id)
    ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ split₁³ ⟩
  (α⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (φ ⊗₁ id)
    ≈˘⟨ refl⟩∘⟨ assoc²βε ⟩
  (α⇒ ⊗₁ id) ∘ φ ∘ (φ ⊗₁ id)                                                  ∎
  where
    -- The hexagon's trailing `α⇐`, met by the `α⇒` we started with.
    tail-cancel : │⟦_⟧ {Z} (α⇐ {X} {Y} {B}) ∘ α⇒ ≈ α⇒ ⊗₁ id
    tail-cancel = begin
      │⟦ α⇐ ⟧ ∘ α⇒             ≈⟨ ⟦⟧-α⇐ ⟩∘⟨refl ⟩
      ((α⇒ ⊗₁ id) ∘ α⇐) ∘ α⇒   ≈⟨ cancelʳ associator.isoˡ ⟩
      α⇒ ⊗₁ id                 ∎

------------------------------------------------------------------------------
-- Evaluation.

-- Close the `X ⁻¹`/`X` pair sitting to the right of a spectator `Z` with the
-- counit.  `capᵗʳ` is the same map with the two wires braided first, so `φ` — and
-- nothing else — separates them.
--
--         Z                                  Z
--         │                                  │
--         │   ╭───────────╮                  │
--         │   │           │      ← ε         │
--         Z  X ⁻¹         X                  Z

ev : ∀ {Z X} → (Z ⊗₀ X ⁻¹) ⊗₀ X ⇒ Z
ev = cap-closeʳ ε ∘ α⇒

capᵗʳ-φ : capᵗʳ {B} {X} ∘ φ ≈ ev
capᵗʳ-φ = begin
  capᵗʳ ∘ φ                          ≈⟨ capᵗʳ-fold ⟩∘⟨refl ⟩
  (cap-closeʳ capʳ ∘ α⇒) ∘ φ         ≈⟨ pullʳ (cancelˡ associator.isoʳ) ⟩
  cap-closeʳ capʳ ∘ (id ⊗₁ σ⇒) ∘ α⇒  ≈⟨ pullʳ (pullˡ merge₂ˡ) ⟩
  ρ⇒ ∘ (id ⊗₁ (capʳ ∘ σ⇒)) ∘ α⇒      ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ cancelʳ commutative) ⟩∘⟨refl ⟩
  ρ⇒ ∘ (id ⊗₁ ε) ∘ α⇒                ≈⟨ sym-assoc ⟩
  ev                                 ∎

ev-natural : {g : Y ⇒ Z} → ev {X = X} ∘ ((g ⊗₁ id) ⊗₁ id) ≈ g ∘ ev
ev-natural {g = g} = begin
  (cap-closeʳ ε ∘ α⇒) ∘ ((g ⊗₁ id) ⊗₁ id)  ≈⟨ pullʳ α⇒-⊗id-commute ⟩
  cap-closeʳ ε ∘ (g ⊗₁ id) ∘ α⇒            ≈⟨ extendʳ spectator-slide ⟩
  g ∘ cap-closeʳ ε ∘ α⇒                    ∎
  where
    -- A map on the spectator slides straight through the cap.
    spectator-slide : cap-closeʳ (ε {X}) ∘ (g ⊗₁ id) ≈ g ∘ cap-closeʳ ε
    spectator-slide = begin
      (ρ⇒ ∘ (id ⊗₁ ε)) ∘ (g ⊗₁ id)  ≈⟨ pullʳ (⟺ whisker-comm) ⟩
      ρ⇒ ∘ (g ⊗₁ id) ∘ (id ⊗₁ ε)    ≈⟨ extendʳ unitorʳ-commute-from ⟩
      g ∘ ρ⇒ ∘ (id ⊗₁ ε)            ∎

-- The cup, met by `ev`, is the snake: the cup plants an `X`/`X ⁻¹` pair, `ε`
-- closes the `X ⁻¹` against the incoming wire, and the wire is left alone.  The
-- spectator `A` never meets either bend.
ev-cupᵗʳ : ev {A ⊗₀ X} {X} ∘ (cupᵗʳ {A} {X} ⊗₁ id {X}) ≈ id
ev-cupᵗʳ {A} {X} = begin
  (cap-closeʳ ε ∘ α⇒) ∘ ((α⇐ ∘ cup-openʳ η) ⊗₁ id)
    ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
  (cap-closeʳ ε ∘ α⇒) ∘ (α⇐ ⊗₁ id) ∘ (cup-openʳ η ⊗₁ id)
    ≈⟨ assoc ⟩
  cap-closeʳ ε ∘ α⇒ ∘ (α⇐ ⊗₁ id) ∘ (cup-openʳ η ⊗₁ id)
    ≈⟨ refl⟩∘⟨ pullˡ assoc-from-coherence ⟩
  cap-closeʳ ε ∘ (α⇐ ∘ (id ⊗₁ α⇒) ∘ α⇒) ∘ (cup-openʳ η ⊗₁ id)
    ≈⟨ refl⟩∘⟨ assoc²βε ⟩
  cap-closeʳ ε ∘ α⇐ ∘ (id ⊗₁ α⇒) ∘ α⇒ ∘ (cup-openʳ η ⊗₁ id)
    ≈⟨ pullˡ cap-closeʳ-natural ⟩
  (id ⊗₁ cap-closeʳ ε) ∘ (id ⊗₁ α⇒) ∘ α⇒ ∘ (cup-openʳ η ⊗₁ id)
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cup-openʳ-whisker ⟩
  (id ⊗₁ cap-closeʳ ε) ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ cup-openˡ η)
    ≈⟨ refl⟩∘⟨ merge₂ˡ ⟩
  (id ⊗₁ cap-closeʳ ε) ∘ (id ⊗₁ (α⇒ ∘ cup-openˡ η))
    ≈⟨ merge₂ˡ ⟩
  id {A} ⊗₁ (cap-closeʳ {A = X} (ε {X}) ∘ α⇒ ∘ cup-openˡ η)
    ≈⟨ refl⟩⊗⟨ (assoc ○ snake₁) ⟩
  id ⊗₁ id
    ≈⟨ ⊗.identity ⟩
  id                                                        ∎

------------------------------------------------------------------------------
-- The name of a map, and how `ev` reads it back.

-- Bend `f`'s input leg around with the cup.  `trace f` is `capᵗʳ` applied to the
-- result — that is the definition of the canonical trace, read differently.
name : A ⊗₀ X ⇒ B ⊗₀ X → A ⇒ (B ⊗₀ X) ⊗₀ X ⁻¹
name f = (f ⊗₁ id) ∘ cupᵗʳ

trace-name : {f : A ⊗₀ X ⇒ B ⊗₀ X} → trace f ≈ capᵗʳ ∘ name f
trace-name = Equiv.refl

-- ... and `f` is recovered from its name: the cup it was bent around is
-- straightened out again by `ev`.
ev-name : {f : A ⊗₀ X ⇒ B ⊗₀ X} → ev {B ⊗₀ X} {X} ∘ (name f ⊗₁ id {X}) ≈ f
ev-name {f = f} = begin
  ev ∘ (((f ⊗₁ id) ∘ cupᵗʳ) ⊗₁ id)        ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
  ev ∘ ((f ⊗₁ id) ⊗₁ id) ∘ (cupᵗʳ ⊗₁ id)  ≈⟨ pullˡ ev-natural ⟩
  (f ∘ ev) ∘ (cupᵗʳ ⊗₁ id)                ≈⟨ pullʳ ev-cupᵗʳ ⟩
  f ∘ id                                  ≈⟨ identityʳ ⟩
  f                                       ∎

------------------------------------------------------------------------------
-- `ev` is `capᵗʳ` with the two `X` wires crossed.

-- The crossing itself: braid the incoming `X` past `X ⁻¹`, past the traced `X`,
-- and back.  Conjugating by `φ` is what puts the two `X`s side by side.
swap : ((B ⊗₀ X) ⊗₀ X ⁻¹) ⊗₀ X ⇒ ((B ⊗₀ X) ⊗₀ X ⁻¹) ⊗₀ X
swap = (φ ⊗₁ id) ∘ φ ∘ (φ ⊗₁ id)

private
  -- Braiding a wire past the unit and closing it on the left is closing it where
  -- it was: the unitors' own coherence, with the spectator watching.
  ρ-φ : (ρ⇒ {B} ⊗₁ id {X}) ∘ φ ≈ ρ⇒
  ρ-φ = begin
    (ρ⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩⊗⟨ braiding-coherence-σ) ⟩∘⟨refl ⟩
    (ρ⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ (λ⇐ ∘ ρ⇒)) ∘ α⇒   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
    (ρ⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ λ⇐) ∘ (id ⊗₁ ρ⇒) ∘ α⇒
      ≈⟨ refl⟩∘⟨ pullˡ triangle-inv ⟩
    (ρ⇒ ⊗₁ id) ∘ (ρ⇐ ⊗₁ id) ∘ (id ⊗₁ ρ⇒) ∘ α⇒  ≈⟨ pullˡ (⊗-cancel unitorʳ.isoʳ identity²) ⟩
    id ∘ (id ⊗₁ ρ⇒) ∘ α⇒                       ≈⟨ identityˡ ⟩
    (id ⊗₁ ρ⇒) ∘ α⇒                            ≈˘⟨ ρ⇒-assoc ⟩∘⟨refl ⟩
    (ρ⇒ ∘ α⇐) ∘ α⇒                             ≈⟨ cancelʳ associator.isoˡ ⟩
    ρ⇒                                         ∎

ev-swap : ev {B ⊗₀ X} {X} ≈ (capᵗʳ ⊗₁ id) ∘ swap
ev-swap = ⟺ (begin
  (capᵗʳ ⊗₁ id) ∘ (φ ⊗₁ id) ∘ φ ∘ (φ ⊗₁ id)    ≈⟨ pullˡ merge₁ˡ ⟩
  ((capᵗʳ ∘ φ) ⊗₁ id) ∘ φ ∘ (φ ⊗₁ id)          ≈⟨ (capᵗʳ-φ ⟩⊗⟨refl) ⟩∘⟨refl ⟩
  ((cap-closeʳ ε ∘ α⇒) ⊗₁ id) ∘ φ ∘ (φ ⊗₁ id)  ≈⟨ split₁ˡ ⟩∘⟨refl ⟩
  ((cap-closeʳ ε ⊗₁ id) ∘ (α⇒ ⊗₁ id)) ∘ φ ∘ (φ ⊗₁ id)
    ≈⟨ assoc ⟩
  (cap-closeʳ ε ⊗₁ id) ∘ (α⇒ ⊗₁ id) ∘ φ ∘ (φ ⊗₁ id)
    ≈˘⟨ refl⟩∘⟨ φ-fuse ⟩
  (cap-closeʳ ε ⊗₁ id) ∘ φ ∘ α⇒                ≈⟨ split₁ˡ ⟩∘⟨refl ⟩
  ((ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ ε) ⊗₁ id)) ∘ φ ∘ α⇒    ≈⟨ assoc ⟩
  (ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ ε) ⊗₁ id) ∘ φ ∘ α⇒
    ≈⟨ refl⟩∘⟨ extendʳ (⟺ φ-natural) ⟩
  (ρ⇒ ⊗₁ id) ∘ φ ∘ (id ⊗₁ ε) ∘ α⇒              ≈⟨ pullˡ ρ-φ ⟩
  ρ⇒ ∘ (id ⊗₁ ε) ∘ α⇒                          ≈⟨ sym-assoc ⟩
  (ρ⇒ ∘ (id ⊗₁ ε)) ∘ α⇒                        ∎)

------------------------------------------------------------------------------
-- Uniqueness.  `Tr` is *any* operation satisfying the JSV axioms *at the traced
-- object `W`* — and only four of those axioms are needed: sliding and the two
-- vanishings never appear.  `W` is fixed rather than quantified so that
-- `Trace.Construction` can reuse this at `W = X ⊗₀ Y` (where the double trace is
-- an operation only over tensors) to derive `vanishing₂`.

module UniqueAt {W : Obj}
    (Tr : ∀ {A B} → A ⊗₀ W ⇒ B ⊗₀ W → A ⇒ B)
    (Tr-resp-≈ : ∀ {A B} {f g : A ⊗₀ W ⇒ B ⊗₀ W} → f ≈ g → Tr f ≈ Tr g)
    (tightenₗ : ∀ {A B C} {f : B ⇒ C} {g : A ⊗₀ W ⇒ B ⊗₀ W} →
                Tr ((f ⊗₁ id) ∘ g) ≈ f ∘ Tr g)
    (tightenᵣ : ∀ {A B C} {f : B ⊗₀ W ⇒ C ⊗₀ W} {g : A ⇒ B} →
                Tr (f ∘ (g ⊗₁ id)) ≈ Tr f ∘ g)
    (superposing : ∀ {Y A B} {f : A ⊗₀ W ⇒ B ⊗₀ W} →
                   Tr (α⇐ ∘ (id {Y} ⊗₁ f) ∘ α⇒) ≈ id {Y} ⊗₁ Tr f)
    (yanking : Tr (σ⇒ {W} {W}) ≈ id)
    where

  -- The crossing traces out to nothing.  Superposing is stated for exactly the
  -- shape `│⟦_⟧` builds, so the middle `φ` traces to `id ⊗₁ Tr σ⇒`; yanking
  -- straightens that, leaving `φ` against its own inverse.
  Tr-swap : Tr (swap {B} {W}) ≈ id
  Tr-swap = begin
    Tr ((φ ⊗₁ id) ∘ φ ∘ (φ ⊗₁ id))  ≈⟨ tightenₗ ⟩
    φ ∘ Tr (φ ∘ (φ ⊗₁ id))          ≈⟨ refl⟩∘⟨ tightenᵣ ⟩
    φ ∘ Tr │⟦ σ⇒ ⟧ ∘ φ              ≈⟨ refl⟩∘⟨ superposing ⟩∘⟨refl ⟩
    φ ∘ (id ⊗₁ Tr σ⇒) ∘ φ           ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ yanking) ⟩∘⟨refl ⟩
    φ ∘ (id ⊗₁ id) ∘ φ              ≈⟨ refl⟩∘⟨ elimˡ ⊗.identity ⟩
    φ ∘ φ                           ≈⟨ φ-inv ⟩
    id                              ∎

  -- Hence the trace of `ev` is `capᵗʳ` — for *any* trace.
  Tr-ev : Tr (ev {B ⊗₀ W} {W}) ≈ capᵗʳ
  Tr-ev = begin
    Tr ev                      ≈⟨ Tr-resp-≈ ev-swap ⟩
    Tr ((capᵗʳ ⊗₁ id) ∘ swap)  ≈⟨ tightenₗ ⟩
    capᵗʳ ∘ Tr swap            ≈⟨ refl⟩∘⟨ Tr-swap ⟩
    capᵗʳ ∘ id                 ≈⟨ identityʳ ⟩
    capᵗʳ                      ∎

  -- Uniqueness: `Tr` agrees with the canonical trace.
  trace-unique : {f : A ⊗₀ W ⇒ B ⊗₀ W} → Tr f ≈ trace f
  trace-unique = begin
    Tr _                      ≈˘⟨ Tr-resp-≈ ev-name ⟩
    Tr (ev ∘ (name _ ⊗₁ id))  ≈⟨ tightenᵣ ⟩
    Tr ev ∘ name _            ≈⟨ Tr-ev ⟩∘⟨refl ⟩
    capᵗʳ ∘ name _            ≈˘⟨ trace-name ⟩
    trace _                   ∎

------------------------------------------------------------------------------
-- The headline: a pre-trace over this category's symmetric structure is the
-- canonical cap-cup trace.

pretrace-unique : (P : PreTrace symmetric)
    {f : A ⊗₀ X ⇒ B ⊗₀ X} → PreTrace.trace P f ≈ trace f
pretrace-unique P =
  UniqueAt.trace-unique Tr Tr-resp-≈ tightenₗ tightenᵣ superposing yanking
  where open PreTrace P renaming (trace to Tr; trace-resp-≈ to Tr-resp-≈)
