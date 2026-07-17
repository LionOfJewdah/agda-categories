{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Monoidal.Rigid using (LeftRigid)
open import Categories.Category.Monoidal.CompactClosed using (CompactClosed)

module Categories.Category.Monoidal.CompactClosed.Trace
    {o ℓ e} {𝒞 : Category o ℓ e}
    (M : Monoidal 𝒞)
    (K : CompactClosed M) where

-- The trace of `f : A ⊗₀ X ⇒ B ⊗₀ X` in a compact closed category: bend the `X` leg
-- around through a cup and a cap.  This file builds it, proves every JSV axiom, and
-- shows it is the *unique* such operation (`pretrace-unique`) — from which `vanishing₂`
-- falls out.  Joyal, Street & Verity (1996), §5; uniqueness after Hasegawa, MSCS 19(2)
-- (2009), Appendix B.

open Category 𝒞
open Monoidal M
open CompactClosed K using (symmetric; leftRigid)
open Symmetric symmetric using (braiding; commutative; hexagon₁; hexagon₂)
open LeftRigid leftRigid using (_⁻¹; η; ε; snake₁; dual₁)
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Morphism.Reasoning 𝒞
open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Braided.Properties (Symmetric.braided symmetric)
  using (braiding-coherence-σ; braiding-coherence-σ′) renaming (module Shorthands to BraidShorthands)
open import Categories.Category.Monoidal.Rigid.Dual M leftRigid
  using (dual₁-cap; dual₁-cup)
open import Categories.Category.Monoidal.Reassociation M
open import Categories.Category.Monoidal.CupCap M
open import Categories.Category.Monoidal.Traced.PreTrace M using (PreTrace)
open import Categories.Category.Monoidal.Utilities M as MonUtil
open MonUtil.Shorthands
open BraidShorthands using (σ⇒; σ⇒-comm)

private
  variable
    A B C W X Y Z : Obj

  whisker-id : {f : X ⇒ X} → f ≈ id → id {A} ⊗₁ f ≈ id
  whisker-id f≈id = (refl⟩⊗⟨ f≈id) ○ ⊗.identity

-- Diagrams read bottom-to-top: inputs enter below and outputs leave above.  Duality
-- bends a wire: `η` grows an `X`/`X ⁻¹` pair, while `ε` swallows one back.  `capᵗʳ`
-- and `cupᵗʳ` are those bends with a spectator wire passing alongside.
--
--                capᵗʳ                              cupᵗʳ
--
--         B                                  A      X       X ⁻¹
--         │                                  │      │        │
--         │      ╭──────────────╮            │      ╰────────╯     ← η
--         │      │              │            │
--         B      X            X ⁻¹           A
--                   ↑ ε ∘ σ⇒

capʳ : X ⊗₀ X ⁻¹ ⇒ unit
capʳ = ε ∘ σ⇒

capᵗʳ : (B ⊗₀ X) ⊗₀ X ⁻¹ ⇒ B
capᵗʳ = cap-bendʳ capʳ

cupᵗʳ : A ⇒ (A ⊗₀ X) ⊗₀ X ⁻¹
cupᵗʳ = cup-bendʳ η

-- The trace closes `f`'s right wire `X` through its dual X⁻¹.
--
--                      B
--                      │
--          ┌───────────┴────────────┐
--          │          capᵗʳ         │       ← ε ∘ σ⇒
--          └────┬─────────┬───────┬─┘
--               B         X      X ⁻¹
--          ┌────┴─────────┴──┐    │
--          │        f        │    │
--          └────┬─────────┬──┘    │
--               A         X      X ⁻¹
--          ┌────┴─────────┴───────┴─┐
--          │          cupᵗʳ         │       ← η
--          └───────────┬────────────┘
--                      A

trace-expanded : A ⊗₀ X ⇒ B ⊗₀ X → A ⇒ B
trace-expanded f =
  ρ⇒ ∘ (id ⊗₁  ε)
     ∘ (id ⊗₁ σ⇒) ∘ α⇒
     ∘ (f  ⊗₁ id) ∘ α⇐
     ∘ (id ⊗₁  η) ∘ ρ⇐

trace : A ⊗₀ X ⇒ B ⊗₀ X → A ⇒ B
trace f = capᵗʳ ∘ (f ⊗₁ id) ∘ cupᵗʳ

trace-resp-≈ : {f g : A ⊗₀ X ⇒ B ⊗₀ X} → f ≈ g → trace f ≈ trace g
trace-resp-≈ f≈g = refl⟩∘⟨ (f≈g ⟩⊗⟨refl) ⟩∘⟨refl

private
  capᵗʳ-expand : capᵗʳ {B} {X} ≈ ρ⇒ ∘ (id ⊗₁ ε) ∘ (id ⊗₁ σ⇒) ∘ α⇒
  capᵗʳ-expand = begin
    capᵗʳ                                     ≈˘⟨ cap-closeʳ-∘ ε ⟩∘⟨refl ⟩
    (cap-closeʳ ε ∘ (id ⊗₁ σ⇒)) ∘ α⇒          ≈⟨ assoc²αε ⟩
    ρ⇒ ∘ (id ⊗₁ ε) ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∎

  trace⟨_⟩ : {f g : A ⊗₀ X ⇒ B ⊗₀ X} → f ≈ g → trace f ≈ trace g
  trace⟨_⟩ = trace-resp-≈

  -- Congruence for a double trace — over `X` of a trace over `Y`; used for `vanishing₂`.
  trace²⟨_⟩ : {f g : (A ⊗₀ X) ⊗₀ Y ⇒ (B ⊗₀ X) ⊗₀ Y} → f ≈ g → trace (trace f) ≈ trace (trace g)
  trace²⟨ f≈g ⟩ = trace⟨ trace⟨ f≈g ⟩ ⟩

trace-expand : {f : A ⊗₀ X ⇒ B ⊗₀ X} → trace f ≈ trace-expanded f
trace-expand = (capᵗʳ-expand ⟩∘⟨refl) ○ ⟺ reassoc-tail₅

private
  cupᵗʳ-slide : {g : X ⇒ Y} →
    ((id {A} ⊗₁ g) ⊗₁ id) ∘ cupᵗʳ ≈ (id ⊗₁ dual₁ g) ∘ cupᵗʳ
  cupᵗʳ-slide {g = g} = begin
    ((id ⊗₁ g) ⊗₁ id) ∘ cupᵗʳ                    ≈⟨ cup-bendʳ-⊗ η ⟩
    cup-bendʳ ((g ⊗₁ id) ∘ η)                    ≈⟨ cup-bendʳ-resp (⟺ dual₁-cup) ⟩
    cup-bendʳ ((id ⊗₁ dual₁ g) ∘ η)              ≈˘⟨ cup-bendʳ-⊗ η ⟩
    ((id ⊗₁ id) ⊗₁ dual₁ g) ∘ cupᵗʳ              ≈⟨ (⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl ⟩
    (id ⊗₁ dual₁ g) ∘ cupᵗʳ                      ∎

  -- Evaluation after swapping is natural in the wire being evaluated.
  capʳ-natural : {g : X ⇒ Y} →
    capʳ {X} ∘ (id ⊗₁ dual₁ g) ≈ capʳ {Y} ∘ (g ⊗₁ id)
  capʳ-natural {g = g} = begin
    (ε ∘ σ⇒) ∘ (id ⊗₁ dual₁ g)  ≈⟨ pullʳ σ⇒-comm ⟩
    ε ∘ ((dual₁ g ⊗₁ id) ∘ σ⇒)  ≈⟨ extendʳ dual₁-cap ⟩
    ε ∘ ((id ⊗₁ g) ∘ σ⇒)        ≈˘⟨ pullʳ σ⇒-comm ⟩
    (ε ∘ σ⇒) ∘ (g ⊗₁ id)        ∎

  capᵗʳ-slide : {g : X ⇒ Y} →
    capᵗʳ ∘ (id {B ⊗₀ X} ⊗₁ dual₁ g) ≈ capᵗʳ ∘ ((id ⊗₁ g) ⊗₁ id)
  capᵗʳ-slide {g = g} = begin
    capᵗʳ ∘ (id ⊗₁ dual₁ g)                    ≈˘⟨ refl⟩∘⟨ (⊗.identity ⟩⊗⟨refl) ⟩
    capᵗʳ ∘ ((id ⊗₁ id) ⊗₁ dual₁ g)            ≈⟨ cap-bendʳ-⊗ capʳ ⟩
    cap-bendʳ (capʳ ∘ (id ⊗₁ dual₁ g))          ≈⟨ cap-bendʳ-resp capʳ-natural ⟩
    cap-bendʳ (capʳ ∘ (g ⊗₁ id))                ≈˘⟨ cap-bendʳ-⊗ capʳ ⟩
    capᵗʳ ∘ ((id ⊗₁ g) ⊗₁ id)                  ∎

trace-slide : {f : A ⊗₀ Y ⇒ B ⊗₀ X} {g : X ⇒ Y} →
  trace (f ∘ id ⊗₁ g) ≈ trace (id ⊗₁ g ∘ f)
trace-slide {f = f} {g} = begin
  trace (f ∘ id ⊗₁ g)                                   ≈⟨ refl⟩∘⟨ split₁ʳ ⟩∘⟨refl ⟩
  capᵗʳ ∘ (((f ⊗₁ id) ∘ ((id ⊗₁ g) ⊗₁ id)) ∘ cupᵗʳ)     ≈⟨ refl⟩∘⟨ pullʳ cupᵗʳ-slide ⟩
  capᵗʳ ∘ ((f ⊗₁ id) ∘ ((id ⊗₁ dual₁ g) ∘ cupᵗʳ))       ≈⟨ refl⟩∘⟨ extendʳ whisker-comm ⟩
  capᵗʳ ∘ ((id ⊗₁ dual₁ g) ∘ ((f ⊗₁ id) ∘ cupᵗʳ))       ≈⟨ pullˡ capᵗʳ-slide ⟩
  (capᵗʳ ∘ ((id ⊗₁ g) ⊗₁ id)) ∘ ((f ⊗₁ id) ∘ cupᵗʳ)     ≈⟨ center merge₁ʳ ⟩
  trace (id ⊗₁ g ∘ f)                                   ∎

tightenₗ : {f : B ⇒ C} {g : A ⊗₀ X ⇒ B ⊗₀ X} → trace (f ⊗₁ id ∘ g) ≈ f ∘ trace g
tightenₗ {f = f} {g} = begin
  trace (f ⊗₁ id ∘ g)                                ≈⟨ refl⟩∘⟨ pushˡ split₁ʳ ⟩
  capᵗʳ ∘ (((f ⊗₁ id) ⊗₁ id) ∘ ((g ⊗₁ id) ∘ cupᵗʳ))  ≈⟨ extendʳ (cap-bendʳ-commute capʳ) ⟩
  f ∘ trace g                                        ∎

tightenᵣ : {f : B ⊗₀ X ⇒ C ⊗₀ X} {g : A ⇒ B} → trace (f ∘ g ⊗₁ id) ≈ trace f ∘ g
tightenᵣ {f = f} {g} = begin
  trace (f ∘ g ⊗₁ id)                                   ≈⟨ refl⟩∘⟨ split₁ˡ ⟩∘⟨refl ⟩
  capᵗʳ ∘ (((f ⊗₁ id) ∘ ((g ⊗₁ id) ⊗₁ id)) ∘ cupᵗʳ)     ≈⟨ refl⟩∘⟨ pullʳ (cup-bendʳ-commute η) ⟩
  capᵗʳ ∘ ((f ⊗₁ id) ∘ (cupᵗʳ ∘ g))                     ≈⟨ assoc²εβ ⟩
  trace f ∘ g                                           ∎

-- Yanking: closing either output of the symmetry gives the identity.
--
--         X       X ──────────╮                      X
--          ╲     ╱            │                      │
--           ╲   ╱             │                      │
--            ╲ ╱              │                      │
--             ╳               │           =          │
--            ╱ ╲              │                      │
--           ╱   ╲             │                      │
--          ╱     ╲            │                      │
--         X       X ──────────╯                      X
--
--                trace σ⇒                            id

private
  -- Once the cup has been braided to the far side of the loop it sits over the
  -- unit, where `σ⇒ ∘ ρ⇐` and `λ⇐` agree.
  cup-σ-unit : ((η {X} ⊗₁ id {X}) ∘ σ⇒ {X} {unit}) ∘ ρ⇐ ≈ (η ⊗₁ id) ∘ λ⇐
  cup-σ-unit = begin
    ((η ⊗₁ id) ∘ σ⇒) ∘ ρ⇐          ≈⟨ (refl⟩∘⟨ braiding-coherence-σ) ⟩∘⟨refl ⟩
    ((η ⊗₁ id) ∘ (λ⇐ ∘ ρ⇒)) ∘ ρ⇐   ≈⟨ pullʳ (cancelʳ unitorʳ.isoʳ) ⟩
    (η ⊗₁ id) ∘ λ⇐                 ∎

  -- Braiding `X` past `Y`, then past `Z`, is braiding it past `Y ⊗₀ Z` in one go.
  -- `yanking` reads this forwards to collapse its loop; `φ-fuse` reads it backwards.
  braid-loop-collapse :
      (id {Y} ⊗₁ σ⇒ {X} {Z}) ∘ α⇒ ∘ (σ⇒ {X} {Y} ⊗₁ id) ∘ α⇐
      ≈ α⇒ ∘ σ⇒
  braid-loop-collapse = begin
    (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐       ≈⟨ assoc²εβ ⟩
    ((id ⊗₁ σ⇒) ∘ (α⇒ ∘ (σ⇒ ⊗₁ id))) ∘ α⇐   ≈⟨ hexagon₁ ⟩∘⟨refl ⟩
    (α⇒ ∘ (σ⇒ ∘ α⇒)) ∘ α⇐                   ≈⟨ pullʳ (cancelʳ associator.isoʳ) ⟩
    α⇒ ∘ σ⇒                                 ∎

yanking : trace (σ⇒ {X} {X}) ≈ id
yanking = begin
  trace (σ⇒)                                              ≈⟨ trace-expand ⟩
  ρ⇒ ∘ (id ⊗₁ ε) ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ η) ∘ ρ⇐
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ reassoc-tail₅ ⟩
  ρ⇒ ∘ (id ⊗₁ ε) ∘ (((id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ η) ∘ ρ⇐)
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ braid-loop-collapse ⟩∘⟨refl ⟩
  ρ⇒ ∘ (id ⊗₁ ε) ∘ ((α⇒ ∘ σ⇒) ∘ (id ⊗₁ η) ∘ ρ⇐)
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullʳ (pullˡ (braiding.⇒.commute _)) ⟩
  ρ⇒ ∘ (id ⊗₁ ε) ∘ α⇒ ∘ ((η ⊗₁ id) ∘ σ⇒) ∘ ρ⇐
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ cup-σ-unit ⟩
  ρ⇒ ∘ (id ⊗₁ ε) ∘ α⇒ ∘ (η ⊗₁ id) ∘ λ⇐                            ≈⟨ snake₁ ⟩
  id                                                             ∎

-- Vanishing₁: the tensor unit has trivial trace dimension.
--
--         B      unit ────────╮                      B
--         │        │          │                      │
--      ┌──┴────────┴──┐       │                 ┌────┴────┐
--      │       f      │       │        =        │    f    │
--      └──┬────────┬──┘       │                 └────┬────┘
--         │        │          │                      │
--         A      unit ────────╯                      A
--
--     trace (f ⊗₁ id {unit})                         f

private
  -- The unit object has dimension `id`: its loop `ε ∘ σ⇒ ∘ η` is a snake in disguise.
  unit-dimension : ε {unit} ∘ σ⇒ ∘ η ≈ id
  unit-dimension = begin
    ε ∘ σ⇒ ∘ η                              ≈⟨ refl⟩∘⟨ braiding-coherence-σ′ ⟩∘⟨refl ⟩
    ε ∘ (ρ⇐ ∘ λ⇒) ∘ η                       ≈˘⟨ refl⟩∘⟨ λ⇒-ρ⇐-comm ⟩∘⟨refl ⟩
    ε ∘ (λ⇒ ∘ α⇒ ∘ ρ⇐) ∘ η                  ≈⟨ refl⟩∘⟨ pullʳ (pullʳ unitorʳ-commute-to) ⟩
    ε ∘ λ⇒ ∘ α⇒ ∘ (η ⊗₁ id) ∘ ρ⇐            ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ coherence-inv₃ ⟩
    ε ∘ λ⇒ ∘ α⇒ ∘ (η ⊗₁ id) ∘ λ⇐            ≈⟨ pullˡ (⟺ unitorˡ-commute-from) ⟩
    (λ⇒ ∘ (id ⊗₁ ε)) ∘ α⇒ ∘ (η ⊗₁ id) ∘ λ⇐  ≈⟨ (coherence₃ ⟩∘⟨refl) ⟩∘⟨refl ⟩
    (ρ⇒ ∘ (id ⊗₁ ε)) ∘ α⇒ ∘ (η ⊗₁ id) ∘ λ⇐  ≈⟨ assoc ⟩
    ρ⇒ ∘ (id ⊗₁ ε) ∘ α⇒ ∘ (η ⊗₁ id) ∘ λ⇐    ≈⟨ snake₁ ⟩
    id                                      ∎

  ------------------------------------------------------------------------
  -- Bending a wire.  Every trace here opens a cup on the right of `A` with
  -- `cup-openʳ`, runs the map along the resulting loop, and closes a cap with
  -- `cap-closeʳ`; only the cup/cap pair changes.

  ⇒⦑_⦒⇐ : A ⊗₀ X ⇒ B ⊗₀ X → A ⊗₀ (X ⊗₀ Z) ⇒ B ⊗₀ (X ⊗₀ Z)
  ⇒⦑ f ⦒⇐ = α⇒ ∘ (f ⊗₁ id) ∘ α⇐

  -- ... and that associator joins `f`'s whisker to make the loop `⇒⦑ f ⦒⇐`.
  trace-fold : {f : A ⊗₀ X ⇒ B ⊗₀ X} →
    trace f ≈ cap-closeʳ capʳ ∘ ⇒⦑ f ⦒⇐ ∘ cup-openʳ η
  trace-fold = assoc ○ (refl⟩∘⟨ ⟺ assoc²βε)

  -- The loop straightens out, leaving the cup running into the cap.
  trace-unit-id : trace (id {A} ⊗₁ id {unit}) ≈ id
  trace-unit-id = begin
    trace (id ⊗₁ id)                                        ≈⟨ trace⟨ ⊗.identity ⟩ ⟩
    trace id                                                ≈⟨ elim-center ⊗.identity ⟩
    capᵗʳ ∘ cupᵗʳ                                          ≈⟨ cancelInner associator.isoʳ ⟩
    cap-closeʳ capʳ ∘ cup-openʳ η                            ≈⟨ pullˡ (cap-closeʳ-∘ capʳ) ⟩
    cap-closeʳ (capʳ ∘ η) ∘ ρ⇐                              ≈⟨ cap-closeʳ-resp assoc ⟩∘⟨refl ⟩
    cap-closeʳ (ε ∘ σ⇒ ∘ η) ∘ ρ⇐                            ≈⟨ cap-closeʳ-resp unit-dimension ⟩∘⟨refl ⟩
    cap-closeʳ id ∘ ρ⇐                                      ≈⟨ elimʳ ⊗.identity ⟩∘⟨refl ⟩
    ρ⇒ ∘ ρ⇐                                                 ≈⟨ unitorʳ.isoʳ ⟩
    id                                                      ∎

vanishing₁ : {f : A ⇒ B} → trace (f ⊗₁ id {unit}) ≈ f
vanishing₁ {f = f} = begin
  trace (f ⊗₁ id)                   ≈˘⟨ trace⟨ elimʳ ⊗.identity ⟩ ⟩
  trace ((f ⊗₁ id) ∘ (id ⊗₁ id))    ≈⟨ tightenₗ ⟩
  f ∘ trace (id ⊗₁ id)              ≈⟨ elimʳ trace-unit-id ⟩
  f                                 ∎

------------------------------------------------------------------------
-- Superposing: a spectator wire slides past the cap and cup.
--
--     Y      B         X ────────╮            Y          B
--     │      │         │         │            │          │
--     │   ┌──┴─────────┴──┐      │            │       ╭──┴───────────╮
--     │   │       f       │      │      =     │       │   trace f    │
--     │   └──┬─────────┬──┘      │            │       ╰──┬───────────╯
--     │      │         │         │            │          │
--     Y      A         X ────────╯            Y          A
--
--     trace (α⇐ ∘ (id ⊗₁ f) ∘ α⇒)                 id ⊗₁ trace f

superposing : {f : A ⊗₀ X ⇒ B ⊗₀ X} →
  trace (α⇐ ∘ (id {Y} ⊗₁ f) ∘ α⇒) ≈ id ⊗₁ trace f
superposing {f = f} = begin
  capᵗʳ ∘ (⇐f⇒ ⊗₁ id) ∘ α⇐ ∘ cup-openʳ η
    ≈⟨ cap-closeʳ-assoc ⟩∘⟨refl ⟩∘⟨refl ⟩
  (((id ⊗₁ cap-closeʳ capʳ) ∘ α⇒) ∘ α⇒) ∘ (⇐f⇒ ⊗₁ id) ∘ α⇐ ∘ cup-openʳ η
    ≈⟨ assoc²αε ⟩
  (id ⊗₁ cap-closeʳ capʳ) ∘ α⇒ ∘ α⇒ ∘ (⇐f⇒ ⊗₁ id) ∘ α⇐ ∘ cup-openʳ η
    ≈⟨ refl⟩∘⟨ reassoc-tail₅ ⟩
  (id ⊗₁ cap-closeʳ capʳ) ∘ (α⇒ ∘ α⇒ ∘ (⇐f⇒ ⊗₁ id) ∘ α⇐) ∘ cup-openʳ η
    ≈⟨ refl⟩∘⟨ α-conj-slide ⟩∘⟨refl ⟩
  (id ⊗₁ cap-closeʳ capʳ) ∘ ((id ⊗₁ ⇒⦑ f ⦒⇐) ∘ α⇒) ∘ cup-openʳ η
    ≈⟨ refl⟩∘⟨ pullʳ cup-openʳ-natural ⟩
  (id ⊗₁ cap-closeʳ capʳ) ∘ (id ⊗₁ ⇒⦑ f ⦒⇐) ∘ (id ⊗₁ cup-openʳ η)
    ≈⟨ merge₂³ ⟩
  id ⊗₁ (cap-closeʳ capʳ ∘ ⇒⦑ f ⦒⇐ ∘ cup-openʳ η)
    ≈˘⟨ refl⟩⊗⟨ trace-fold ⟩
  id ⊗₁ trace f                           ∎
  where ⇐f⇒ = α⇐ ∘ (id ⊗₁ f) ∘ α⇒

------------------------------------------------------------------------------
-- Uniqueness.  A compact closed category has *exactly one* trace: any operation
-- satisfying the JSV axioms agrees with the canonical trace above.
--
-- Hasegawa, "On traced monoidal closed categories", MSCS 19(2), 2009, Appendix B
-- (Proposition B.1), which proves it for tortile categories; a compact closed
-- category is a tortile one whose twist is the identity.  The proof there is
-- graphical, in four steps; this is its algebraic form.
--
-- Only four trace axioms are used: the two tightenings, superposing and yanking.
-- Sliding and the two vanishings never appear.

module HasegawaTraceUniqueness where
  -- Run a map on the last two wires beside a spectator.  `│⟦ h ⟧` is the picture of
  -- a spectator wire `│` beside the box `h`: re-bracket, run the box, re-bracket back.
  --
  --         Z          A  B
  --         │          │  │
  --         │        ┌─┴──┴─┐
  --         │        │  h   │
  --         │        └─┬──┬─┘
  --         │          │  │
  --         Z          X  Y
  --
  -- Its functoriality keeps the crossing argument below structural.
  │⟦_⟧ : {Z X Y A B : Obj} → X ⊗₀ Y ⇒ A ⊗₀ B → (Z ⊗₀ X) ⊗₀ Y ⇒ (Z ⊗₀ A) ⊗₀ B
  │⟦ h ⟧ = α⇐ ∘ (id ⊗₁ h) ∘ α⇒

  -- The spectator is the one wire the equations cannot infer, so each statement
  -- names it once, in prefix form; every other wire follows from the equation.

  ⟦⟧-resp-≈ : {h k : X ⊗₀ Y ⇒ A ⊗₀ B} → h ≈ k → │⟦_⟧ {Z} h ≈ │⟦ k ⟧
  ⟦⟧-resp-≈ h≈k = refl⟩∘⟨ (refl⟩⊗⟨ h≈k) ⟩∘⟨refl

  -- Functoriality.  The re-bracketing in the middle cancels.
  ⟦⟧-∘ : {h : A ⊗₀ B ⇒ C ⊗₀ W} {k : X ⊗₀ Y ⇒ A ⊗₀ B} →
    │⟦_⟧ {Z} h ∘ │⟦ k ⟧ ≈ │⟦ h ∘ k ⟧
  ⟦⟧-∘ {h = h} {k = k} = begin
    (α⇐ ∘ (id ⊗₁ h) ∘ α⇒) ∘ (α⇐ ∘ (id ⊗₁ k) ∘ α⇒)
      ≈⟨ center (cancelʳ associator.isoʳ) ⟩
    α⇐ ∘ (id ⊗₁ h) ∘ (id ⊗₁ k) ∘ α⇒                ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
    α⇐ ∘ (id ⊗₁ (h ∘ k)) ∘ α⇒                      ∎

  ⟦⟧-factor : {h : A ⊗₀ B ⇒ C ⊗₀ W} {k : X ⊗₀ Y ⇒ A ⊗₀ B}
    {h′ : (Z ⊗₀ A) ⊗₀ B ⇒ (Z ⊗₀ C) ⊗₀ W} →
    │⟦_⟧ {Z} h ≈ h′ → │⟦ h ∘ k ⟧ ≈ h′ ∘ │⟦ k ⟧
  ⟦⟧-factor h≈h′ = ⟺ ⟦⟧-∘ ○ (h≈h′ ⟩∘⟨refl)

  -- Whatever the box becomes past `α⇒` is what the brackets leave behind.
  ⟦⟧-eval : {h : X ⊗₀ Y ⇒ A ⊗₀ B} {k : (Z ⊗₀ X) ⊗₀ Y ⇒ (Z ⊗₀ A) ⊗₀ B} →
    (id ⊗₁ h) ∘ α⇒ ≈ α⇒ ∘ k → │⟦ h ⟧ ≈ k
  ⟦⟧-eval h-past-α = (refl⟩∘⟨ h-past-α) ○ cancelˡ associator.isoˡ

  ⟦⟧-id : │⟦_⟧ {Z} (id {X ⊗₀ Y}) ≈ id
  ⟦⟧-id = ⟦⟧-eval (elimˡ ⊗.identity ○ ⟺ identityʳ)

  -- A box touching only one of the two wires slides out of the brackets.
  ⟦⟧-⊗id : {f : X ⇒ A} → │⟦_⟧ {Z} (f ⊗₁ id {Y}) ≈ (id ⊗₁ f) ⊗₁ id
  ⟦⟧-⊗id = ⟦⟧-eval (⟺ assoc-commute-from)

  ⟦⟧-id⊗ : {f : Y ⇒ B} → │⟦_⟧ {Z} (id {X} ⊗₁ f) ≈ id ⊗₁ f
  ⟦⟧-id⊗ = ⟦⟧-eval (⟺ α⇒-id⊗-commute)

  -- An associator in the box is one outside it.
  ⟦⟧-α⇐ : │⟦_⟧ {Z} (α⇐ {X} {Y} {W}) ≈ (α⇒ ⊗₁ id) ∘ α⇐
  ⟦⟧-α⇐ = ⟦⟧-eval assoc-to-coherence

  ----------------------------------------------------------------------------
  -- The crossing.

  -- Braid the last two wires past the spectator.  `φ` is an involution, because the
  -- braiding is one and `│⟦_⟧` is a functor.
  φ : (Z ⊗₀ X) ⊗₀ Y ⇒ (Z ⊗₀ Y) ⊗₀ X
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
    │⟦ (c ⊗₁ id) ∘ σ⇒ ⟧     ≈⟨ ⟦⟧-factor ⟦⟧-⊗id ⟩
    ((id ⊗₁ c) ⊗₁ id) ∘ φ   ∎

  -- `⟦⟧-α⇐` with the trailing associator cancelled off, as `φ-fuse` meets it.
  ⟦⟧-α⇐-cancel : │⟦_⟧ {Z} (α⇐ {X} {Y} {B}) ∘ α⇒ ≈ α⇒ ⊗₁ id
  ⟦⟧-α⇐-cancel = (⟦⟧-α⇐ ⟩∘⟨refl) ○ cancelʳ associator.isoˡ

  -- The crossing in Hasegawa's picture, and the only place the hexagon is used.
  φ-fuse : φ ∘ α⇒ {Z ⊗₀ X} {Y} {B} ≈ (α⇒ ⊗₁ id) ∘ φ ∘ (φ ⊗₁ id)
  φ-fuse = begin
    │⟦ σ⇒ ⟧ ∘ α⇒
      ≈˘⟨ ⟦⟧-resp-≈ (cancelˡ associator.isoˡ) ⟩∘⟨refl ⟩
    │⟦ α⇐ ∘ α⇒ ∘ σ⇒ ⟧ ∘ α⇒
      ≈˘⟨ ⟦⟧-resp-≈ (refl⟩∘⟨ braid-loop-collapse) ⟩∘⟨refl ⟩
    │⟦ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐ ⟧ ∘ α⇒
      ≈⟨ pushˡ (⟦⟧-factor ⟦⟧-α⇐) ⟩
    ((α⇒ ⊗₁ id) ∘ α⇐) ∘ │⟦ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐ ⟧ ∘ α⇒
      ≈⟨ refl⟩∘⟨ pushˡ (⟦⟧-factor ⟦⟧-id⊗) ⟩
    ((α⇒ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ σ⇒) ∘ │⟦ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐ ⟧ ∘ α⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (⟦⟧-factor (⟺ assoc-from-coherence)) ⟩
    ((α⇒ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ σ⇒) ∘ (α⇒ ∘ (α⇐ ⊗₁ id)) ∘ │⟦ (σ⇒ ⊗₁ id) ∘ α⇐ ⟧ ∘ α⇒
      ≈⟨ assoc ⟩
    (α⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ (α⇒ ∘ (α⇐ ⊗₁ id)) ∘ │⟦ (σ⇒ ⊗₁ id) ∘ α⇐ ⟧ ∘ α⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
    (α⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (α⇐ ⊗₁ id) ∘ │⟦ (σ⇒ ⊗₁ id) ∘ α⇐ ⟧ ∘ α⇒
      ≈˘⟨ refl⟩∘⟨ assoc²βε ⟩
    (α⇒ ⊗₁ id) ∘ φ ∘ (α⇐ ⊗₁ id) ∘ │⟦ (σ⇒ ⊗₁ id) ∘ α⇐ ⟧ ∘ α⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (⟦⟧-factor ⟦⟧-⊗id) ⟩
    (α⇒ ⊗₁ id) ∘ φ ∘ (α⇐ ⊗₁ id) ∘ ((id ⊗₁ σ⇒) ⊗₁ id) ∘ │⟦ α⇐ ⟧ ∘ α⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟦⟧-α⇐-cancel ⟩
    (α⇒ ⊗₁ id) ∘ φ ∘ (α⇐ ⊗₁ id) ∘ ((id ⊗₁ σ⇒) ⊗₁ id) ∘ (α⇒ ⊗₁ id)
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ split₁³ ⟩
    (α⇒ ⊗₁ id) ∘ φ ∘ (φ ⊗₁ id)                                                  ∎

  ----------------------------------------------------------------------------
  -- Evaluation.

  -- Evaluate a dual pair to the right of a spectator.
  ev : (Z ⊗₀ X ⁻¹) ⊗₀ X ⇒ Z
  ev = cap-bendʳ ε

  capᵗʳ-φ : capᵗʳ {B} {X} ∘ φ ≈ ev
  capᵗʳ-φ = begin
    capᵗʳ ∘ φ                                   ≈⟨ pullʳ (cancelˡ associator.isoʳ) ⟩
    cap-closeʳ capʳ ∘ (id ⊗₁ σ⇒) ∘ α⇒          ≈⟨ pullˡ (cap-closeʳ-∘ capʳ) ⟩
    cap-bendʳ (capʳ ∘ σ⇒)                      ≈⟨ cap-bendʳ-resp (cancelʳ commutative) ⟩
    ev                                         ∎

  -- The cup, met by `ev`, is the snake: the cup plants an `X`/`X ⁻¹` pair, `ε`
  -- closes the `X ⁻¹` against the incoming wire, and the wire is left alone.  The
  -- spectator `A` never meets either bend.
  ev-cupᵗʳ : ev {A ⊗₀ X} {X} ∘ (cupᵗʳ ⊗₁ id) ≈ id
  ev-cupᵗʳ = begin
    ev ∘ (cupᵗʳ ⊗₁ id)                                           ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
    ev ∘ (α⇐ ⊗₁ id) ∘ (cup-openʳ η ⊗₁ id)                         ≈⟨ assoc ⟩
    cap-closeʳ ε ∘ α⇒ ∘ (α⇐ ⊗₁ id) ∘ (cup-openʳ η ⊗₁ id)          ≈⟨ refl⟩∘⟨ pullˡ assoc-from-coherence ⟩
    cap-closeʳ ε ∘ (α⇐ ∘ (id ⊗₁ α⇒) ∘ α⇒) ∘ (cup-openʳ η ⊗₁ id)   ≈⟨ refl⟩∘⟨ assoc²βε ⟩
    cap-closeʳ ε ∘ α⇐ ∘ (id ⊗₁ α⇒) ∘ α⇒ ∘ (cup-openʳ η ⊗₁ id)     ≈⟨ pullˡ cap-closeʳ-natural ⟩
    (id ⊗₁ cap-closeʳ ε) ∘ (id ⊗₁ α⇒) ∘ α⇒ ∘ (cup-openʳ η ⊗₁ id)  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cup-openʳ-whisker ⟩
    (id ⊗₁ cap-closeʳ ε) ∘ (id ⊗₁ α⇒) ∘ (id ⊗₁ cup-openˡ η)       ≈⟨ merge₂³ ⟩
    id ⊗₁ (cap-closeʳ ε ∘ α⇒ ∘ cup-openˡ η)                       ≈⟨ refl⟩⊗⟨ assoc ⟩
    id ⊗₁ (ρ⇒ ∘ (id ⊗₁ ε) ∘ α⇒ ∘ (η ⊗₁ id) ∘ λ⇐)                  ≈⟨ whisker-id snake₁ ⟩
    id                                                            ∎

  ----------------------------------------------------------------------------
  -- The name of a map, and how `ev` reads it back.

  -- Bend `f`'s input leg around with the cup.  `trace f` is `capᵗʳ` applied to the
  -- result — that is the definition of the canonical trace, read differently.
  name : A ⊗₀ X ⇒ B ⊗₀ X → A ⇒ (B ⊗₀ X) ⊗₀ X ⁻¹
  name f = (f ⊗₁ id) ∘ cupᵗʳ

  -- ... and `f` is recovered from its name: the cup it was bent around is
  -- straightened out again by `ev`.
  ev-name : {f : A ⊗₀ X ⇒ B ⊗₀ X} → ev {B ⊗₀ X} {X} ∘ (name f ⊗₁ id) ≈ f
  ev-name {f = f} = begin
    ev ∘ (((f ⊗₁ id) ∘ cupᵗʳ) ⊗₁ id)        ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
    ev ∘ ((f ⊗₁ id) ⊗₁ id) ∘ (cupᵗʳ ⊗₁ id)  ≈⟨ pullˡ (cap-bendʳ-commute ε) ⟩
    (f ∘ ev) ∘ (cupᵗʳ ⊗₁ id)                ≈⟨ cancelʳ ev-cupᵗʳ ⟩
    f                                       ∎

  ----------------------------------------------------------------------------
  -- `ev` is `capᵗʳ` with the two `X` wires crossed.

  -- The crossing itself: braid the incoming `X` past `X ⁻¹`, past the traced `X`,
  -- and back.  Conjugating by `φ` is what puts the two `X`s side by side.
  swap : ((B ⊗₀ X) ⊗₀ X ⁻¹) ⊗₀ X ⇒ ((B ⊗₀ X) ⊗₀ X ⁻¹) ⊗₀ X
  swap = (φ ⊗₁ id) ∘ φ ∘ (φ ⊗₁ id)

  -- Braiding a wire past the unit and closing it on the left is closing it where
  -- it was: the unitors' own coherence, with the spectator watching.
  ρ-φ : (ρ⇒ {B} ⊗₁ id {X}) ∘ φ ≈ ρ⇒
  ρ-φ = begin
    (ρ⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒               ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ braiding-coherence-σ ⟩∘⟨refl ⟩
    (ρ⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ (λ⇐ ∘ ρ⇒)) ∘ α⇒        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ split₂ˡ ⟩
    (ρ⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ λ⇐) ∘ (id ⊗₁ ρ⇒) ∘ α⇒  ≈⟨ refl⟩∘⟨ pullˡ triangle-inv ⟩
    (ρ⇒ ⊗₁ id) ∘ (ρ⇐ ⊗₁ id) ∘ (id ⊗₁ ρ⇒) ∘ α⇒       ≈⟨ cancelˡ (⊗-cancel unitorʳ.isoʳ identity²) ⟩
    (id ⊗₁ ρ⇒) ∘ α⇒                                 ≈⟨ coherence₂ ⟩
    ρ⇒                                              ∎

  ev-swap : ev {B ⊗₀ X} {X} ≈ (capᵗʳ ⊗₁ id) ∘ swap
  ev-swap = begin
    ev                                                    ≈⟨ assoc ⟩
    ρ⇒ ∘ (id ⊗₁ ε) ∘ α⇒                                   ≈˘⟨ pullˡ ρ-φ ⟩
    (ρ⇒ ⊗₁ id) ∘ φ ∘ (id ⊗₁ ε) ∘ α⇒                       ≈˘⟨ refl⟩∘⟨ extendʳ (⟺ φ-natural) ⟩
    (ρ⇒ ⊗₁ id) ∘ ((id ⊗₁ ε) ⊗₁ id) ∘ φ ∘ α⇒               ≈⟨ pullˡ merge₁ˡ ⟩
    (cap-closeʳ ε ⊗₁ id) ∘ φ ∘ α⇒                         ≈⟨ refl⟩∘⟨ φ-fuse ⟩
    (cap-closeʳ ε ⊗₁ id) ∘ (α⇒ ⊗₁ id) ∘ φ ∘ (φ ⊗₁ id)     ≈⟨ pullˡ merge₁ˡ ⟩
    (ev ⊗₁ id) ∘ φ ∘ (φ ⊗₁ id)                             ≈˘⟨ capᵗʳ-φ ⟩⊗⟨refl ⟩∘⟨refl ⟩
    ((capᵗʳ ∘ φ) ⊗₁ id) ∘ φ ∘ (φ ⊗₁ id)                   ≈˘⟨ pullˡ merge₁ˡ ⟩
    (capᵗʳ ⊗₁ id) ∘ swap                                  ∎

----------------------------------------------------------------------------
-- `Tr` is *any* operation satisfying the JSV axioms *at the traced object `W`* —
-- and only four are needed: sliding and the two vanishings never appear.  `W` is
-- fixed rather than quantified so the double trace below can reuse this at
-- `W = X ⊗₀ Y` (where it is an operation only over tensors) to derive `vanishing₂`.
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
  open HasegawaTraceUniqueness

  -- The crossing traces out to nothing.  Superposing is stated for exactly the
  -- shape `│⟦_⟧` builds, so the middle `φ` traces to `id ⊗₁ Tr σ⇒`; yanking
  -- straightens that, leaving `φ` against its own inverse.
  Tr-swap : Tr (swap {B} {W}) ≈ id
  Tr-swap = begin
    Tr ((φ ⊗₁ id) ∘ φ ∘ (φ ⊗₁ id))  ≈⟨ tightenₗ ⟩
    φ ∘ Tr (φ ∘ (φ ⊗₁ id))          ≈⟨ refl⟩∘⟨ tightenᵣ ⟩
    φ ∘ Tr │⟦ σ⇒ ⟧ ∘ φ              ≈⟨ refl⟩∘⟨ superposing ⟩∘⟨refl ⟩
    φ ∘ (id ⊗₁ Tr σ⇒) ∘ φ           ≈⟨ elim-center (whisker-id yanking) ⟩
    φ ∘ φ                           ≈⟨ φ-inv ⟩
    id                              ∎

  -- Hence the trace of `ev` is `capᵗʳ` — for *any* trace.
  Tr-ev : Tr (ev {B ⊗₀ W} {W}) ≈ capᵗʳ
  Tr-ev = begin
    Tr ev                      ≈⟨ Tr-resp-≈ ev-swap ⟩
    Tr ((capᵗʳ ⊗₁ id) ∘ swap)  ≈⟨ tightenₗ ⟩
    capᵗʳ ∘ Tr swap            ≈⟨ elimʳ Tr-swap ⟩
    capᵗʳ                      ∎

  -- Uniqueness: `Tr` agrees with the canonical trace.
  trace-unique : {f : A ⊗₀ W ⇒ B ⊗₀ W} → Tr f ≈ trace f
  trace-unique = begin
    Tr _                      ≈˘⟨ Tr-resp-≈ ev-name ⟩
    Tr (ev ∘ (name _ ⊗₁ id))  ≈⟨ tightenᵣ ⟩
    Tr ev ∘ name _            ≈⟨ Tr-ev ⟩∘⟨refl ⟩
    trace _                   ∎

-- The headline: any pre-trace over this category's symmetric structure is the
-- canonical cap-cup trace.
pretrace-unique : (P : PreTrace symmetric)
    {f : A ⊗₀ X ⇒ B ⊗₀ X} → PreTrace.trace P f ≈ trace f
pretrace-unique P = UniqueAt.trace-unique T.trace T.trace-resp-≈
  T.tightenₗ T.tightenᵣ T.superposing T.yanking
  where module T = PreTrace P

------------------------------------------------------------------------
-- Vanishing₂: trace out `Y`, then `X`, or trace out `X ⊗₀ Y` in one step.

-- The double trace over `X ⊗₀ Y`, taken one wire at a time: trace out `Y`, then
-- `X`.  It obeys the four pre-trace axioms, so `UniqueAt` identifies it with the
-- cap-cup trace over `X ⊗₀ Y` — and that is JSV's `vanishing₂`.
module TensorTrace {X Y : Obj} where
  open HasegawaTraceUniqueness using (│⟦_⟧)

  -- Re-bracket a map over `X ⊗₀ Y` into a map whose last wire is `Y`.
  ⇐[_]⇒ : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y) → (A ⊗₀ X) ⊗₀ Y ⇒ (B ⊗₀ X) ⊗₀ Y
  ⇐[ h ]⇒ = α⇐ ∘ h ∘ α⇒

  -- Trace out `Y`, then `X`.
  Tr : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y) → A ⇒ B
  Tr h = trace (trace ⇐[ h ]⇒)

  Tr-resp-≈ : {h k : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} → h ≈ k → Tr h ≈ Tr k
  Tr-resp-≈ h≈k = trace²⟨ refl⟩∘⟨ h≈k ⟩∘⟨refl ⟩

  -- A map tensored beside `X ⊗₀ Y` slides out of both traces.
  Tr-tightenₗ : {f : B ⇒ C} {h : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} →
    Tr ((f ⊗₁ id) ∘ h) ≈ f ∘ Tr h
  Tr-tightenₗ {f = f} {h} = begin
    Tr ((f ⊗₁ id) ∘ h)                            ≈⟨ trace²⟨ rebracket-tightenˡ ⟩ ⟩
    trace (trace (((f ⊗₁ id) ⊗₁ id) ∘ ⇐[ h ]⇒))   ≈⟨ trace⟨ tightenₗ ⟩ ⟩
    trace ((f ⊗₁ id) ∘ trace ⇐[ h ]⇒)             ≈⟨ tightenₗ ⟩
    f ∘ Tr h                                      ∎

  Tr-tightenᵣ : {h : B ⊗₀ (X ⊗₀ Y) ⇒ C ⊗₀ (X ⊗₀ Y)} {g : A ⇒ B} →
    Tr (h ∘ (g ⊗₁ id)) ≈ Tr h ∘ g
  Tr-tightenᵣ {h = h} {g} = begin
    Tr (h ∘ (g ⊗₁ id))                            ≈⟨ trace²⟨ rebracket-tightenʳ ⟩ ⟩
    trace (trace (⇐[ h ]⇒ ∘ ((g ⊗₁ id) ⊗₁ id)))   ≈⟨ trace⟨ tightenᵣ ⟩ ⟩
    trace (trace ⇐[ h ]⇒ ∘ (g ⊗₁ id))             ≈⟨ tightenᵣ ⟩
    Tr h ∘ g                                      ∎

  -- Two nested reassociations expose a `Z`-superposed `⇐[ h ]⇒`.
  rebracket-superposing : {h : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} →
    ⇐[ α⇐ ∘ (id {Z} ⊗₁ h) ∘ α⇒ ]⇒
    ≈ (α⇐ ⊗₁ id) ∘ │⟦ ⇐[ h ]⇒ ⟧ ∘ (α⇒ ⊗₁ id)
  rebracket-superposing {h = h} = begin
    α⇐ ∘ (α⇐ ∘ (id ⊗₁ h) ∘ α⇒) ∘ α⇒              ≈⟨ refl⟩∘⟨ assoc²βε ⟩
    α⇐ ∘ α⇐ ∘ (id ⊗₁ h) ∘ α⇒ ∘ α⇒                ≈⟨ assoc²εα ⟩
    ((α⇐ ∘ α⇐) ∘ (id ⊗₁ h)) ∘ α⇒ ∘ α⇒            ≈˘⟨ refl⟩∘⟨ pentagon ⟩
    ((α⇐ ∘ α⇐) ∘ (id ⊗₁ h)) ∘ (id ⊗₁ α⇒) ∘ α⇒ ∘ (α⇒ ⊗₁ id)
      ≈⟨ center merge₂ˡ ⟩
    (α⇐ ∘ α⇐) ∘ (id ⊗₁ (h ∘ α⇒)) ∘ α⇒ ∘ (α⇒ ⊗₁ id)
      ≈⟨ pushˡ (⟺ pentagon-inv) ⟩
    ((α⇐ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ α⇐) ∘ (id ⊗₁ (h ∘ α⇒)) ∘ α⇒ ∘ (α⇒ ⊗₁ id)
      ≈⟨ pull-center merge₂ˡ ⟩
    ((α⇐ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ (α⇐ ∘ h ∘ α⇒)) ∘ α⇒ ∘ (α⇒ ⊗₁ id)
      ≈⟨ assoc ⟩
    (α⇐ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ (α⇐ ∘ h ∘ α⇒)) ∘ α⇒ ∘ (α⇒ ⊗₁ id)
      ≈⟨ refl⟩∘⟨ assoc²εβ ⟩
    (α⇐ ⊗₁ id) ∘ │⟦ ⇐[ h ]⇒ ⟧ ∘ (α⇒ ⊗₁ id)  ∎

  -- Superposing: a wire `Z` beside both loops slides out.
  Tr-superposing : {h : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} →
    Tr (α⇐ ∘ (id {Z} ⊗₁ h) ∘ α⇒) ≈ id ⊗₁ Tr h
  Tr-superposing {h = h} = begin
    Tr (α⇐ ∘ (id ⊗₁ h) ∘ α⇒)                               ≈⟨ trace²⟨ rebracket-superposing ⟩ ⟩
    trace (trace ((α⇐ ⊗₁ id) ∘ │⟦ ⇐[ h ]⇒ ⟧ ∘ (α⇒ ⊗₁ id)))  ≈⟨ trace⟨ tightenₗ ⟩ ⟩
    trace (α⇐ ∘ trace (│⟦ ⇐[ h ]⇒ ⟧ ∘ (α⇒ ⊗₁ id)))          ≈⟨ trace⟨ refl⟩∘⟨ tightenᵣ ⟩ ⟩
    trace (α⇐ ∘ trace │⟦ ⇐[ h ]⇒ ⟧ ∘ α⇒)                    ≈⟨ trace⟨ refl⟩∘⟨ superposing ⟩∘⟨refl ⟩ ⟩
    trace (α⇐ ∘ (id ⊗₁ trace ⇐[ h ]⇒) ∘ α⇒)                 ≈⟨ superposing ⟩
    id ⊗₁ Tr h                                              ∎

  -- `σ_{X⊗Y,X⊗Y}` peeled by `hexagon₁` into a `Y`-braiding above an `X`-braiding — the
  -- latter whiskered by `id {Y}`, re-associated to the outside for `tightenᵣ`.
  rebracket-σ : ⇐[ σ⇒ {X ⊗₀ Y} {X ⊗₀ Y} ]⇒
        ≈ (α⇐ ∘ α⇐ ∘ (id ⊗₁ σ⇒ {X ⊗₀ Y} {Y}) ∘ α⇒) ∘ (σ⇒ {X ⊗₀ Y} {X} ⊗₁ id)
  rebracket-σ = begin
    α⇐ ∘ σ⇒ ∘ α⇒                              ≈˘⟨ refl⟩∘⟨ cancelˡ associator.isoˡ ⟩
    α⇐ ∘ α⇐ ∘ α⇒ ∘ σ⇒ ∘ α⇒                    ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ hexagon₁ ⟩
    α⇐ ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)    ≈⟨ refl⟩∘⟨ assoc²εβ ⟩
    α⇐ ∘ (α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒) ∘ (σ⇒ ⊗₁ id)  ≈⟨ sym-assoc ⟩
    (α⇐ ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒) ∘ (σ⇒ ⊗₁ id)  ∎

  -- Trace `B` out of `A ⊗₀ B` braided past `B`, leaving `A` braided past `B`
  -- (`hexagon₂` exposes the `σ⇒ {B} {B}` that `superposing`+`yanking` erase).
  trace-σ : trace (α⇐ ∘ σ⇒ {A ⊗₀ B} {B}) ≈ σ⇒ {A} {B}
  trace-σ = begin
    trace (α⇐ ∘ σ⇒)                             ≈⟨ trace⟨ insertʳ associator.isoˡ ⟩ ⟩
    trace (((α⇐ ∘ σ⇒) ∘ α⇐) ∘ α⇒)               ≈˘⟨ trace⟨ hexagon₂ ⟩∘⟨refl ⟩ ⟩
    trace ((((σ⇒ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ σ⇒)) ∘ α⇒)
      ≈⟨ trace⟨ assoc²αε ⟩ ⟩
    trace ((σ⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒)   ≈⟨ tightenₗ ⟩
    σ⇒ ∘ trace (α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒)           ≈⟨ refl⟩∘⟨ superposing ⟩
    σ⇒ ∘ id ⊗₁ trace σ⇒                         ≈⟨ elimʳ (whisker-id yanking) ⟩
    σ⇒                                          ∎

  -- The `Y` trace.  `pentagon-inv` exposes the outer associator; then
  -- `superposing` factors `X` off and `trace-σ` collapses the remaining loop.
  trace-σ-assoc : trace (α⇐ ∘ α⇐ ∘ (id ⊗₁ σ⇒ {X ⊗₀ Y} {Y}) ∘ α⇒) ≈ α⇐ {X} {Y} {X} ∘ (id ⊗₁ σ⇒ {X} {Y})
  trace-σ-assoc = begin
    trace (α⇐ ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒)                 ≈⟨ trace⟨ pullˡ (⟺ pentagon-inv) ⟩ ⟩
    trace ((((α⇐ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ α⇐)) ∘ (id ⊗₁ σ⇒) ∘ α⇒)
      ≈⟨ trace⟨ assoc²αε ⟩ ⟩
    trace ((α⇐ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ α⇐) ∘ (id ⊗₁ σ⇒) ∘ α⇒)
      ≈⟨ trace⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩ ⟩
    trace ((α⇐ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ (α⇐ ∘ σ⇒)) ∘ α⇒)  ≈⟨ tightenₗ ⟩
    α⇐ ∘ trace (α⇐ ∘ (id ⊗₁ (α⇐ ∘ σ⇒)) ∘ α⇒)          ≈⟨ refl⟩∘⟨ superposing ⟩
    α⇐ ∘ (id ⊗₁ trace (α⇐ ∘ σ⇒))                      ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ trace-σ ⟩
    α⇐ ∘ (id ⊗₁ σ⇒)                                   ∎

  Tr-yanking : Tr (σ⇒ {X ⊗₀ Y} {X ⊗₀ Y}) ≈ id
  Tr-yanking = begin
    trace (trace ⇐[ σ⇒ ]⇒)                                    ≈⟨ trace²⟨ rebracket-σ ⟩ ⟩
    trace (trace ((α⇐ ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒) ∘ (σ⇒ ⊗₁ id)))  ≈⟨ trace⟨ tightenᵣ ⟩ ⟩
    trace (trace (α⇐ ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒) ∘ σ⇒)            ≈⟨ trace⟨ trace-σ-assoc ⟩∘⟨refl ⟩ ⟩
    trace ((α⇐ ∘ (id ⊗₁ σ⇒)) ∘ σ⇒)                            ≈⟨ trace⟨ extendˡ (⟺ σ⇒-comm) ⟩ ⟩
    trace ((α⇐ ∘ σ⇒) ∘ (σ⇒ ⊗₁ id))                            ≈⟨ tightenᵣ ⟩
    trace (α⇐ ∘ σ⇒) ∘ σ⇒                                      ≈⟨ trace-σ ⟩∘⟨refl ⟩
    σ⇒ ∘ σ⇒                                                   ≈⟨ commutative ⟩
    id                                                        ∎

vanishing₂ : {h : A ⊗₀ (X ⊗₀ Y) ⇒ B ⊗₀ (X ⊗₀ Y)} → trace (trace (α⇐ ∘ h ∘ α⇒)) ≈ trace h
vanishing₂ =
  UniqueAt.trace-unique Tr Tr-resp-≈ Tr-tightenₗ Tr-tightenᵣ Tr-superposing Tr-yanking
  where open TensorTrace
