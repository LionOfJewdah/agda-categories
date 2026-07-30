{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Monoidal.Traced using (Traced)

-- Shared groundwork for "traced ∗-autonomous categories are compact closed"
-- (Hajgató & Hasegawa, TAC 28(7), 2013, §3).  This module collects the pieces
-- that do not yet depend on the dualizing object: the trace of evaluation `τ`
-- and its dinaturality (Lemma 3.1), the symmetric-closed isomorphisms out of
-- which `φ` is assembled, and Barr's canonical double-dual map `δ` together with
-- the predicate `IsDualizing` that the rest of the development assumes.

module Categories.Category.Monoidal.Star-Autonomous.Traced.Base
  {o ℓ e} {𝒞 : Category o ℓ e} {M : Monoidal 𝒞}
  (Cl : Closed M) (T : Traced M) where

open import Data.Product using (_,_)
open import Relation.Unary using (Pred)

open import Categories.Category.Monoidal.Symmetric M using (Symmetric)

open Category 𝒞
open Monoidal M
open Traced T
  using (trace; trace⟨_⟩; slide; tightenₗ; tightenᵣ; vanishing₁; vanishing₂
        ; superposing; yanking; symmetric)
open Symmetric symmetric using (braiding; commutative; hexagon₁)
open Closed Cl using ([_,_]₀; [_,_]₁; [-,_]; [_,-]; [-,-])

open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Reassociation M
open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Utilities M
open import Categories.Category.Monoidal.Braided.Properties (Symmetric.braided symmetric)
  renaming (module Shorthands to BraidShorthands)
open import Categories.Category.Monoidal.Closed.Properties Cl
open import Categories.Morphism 𝒞 using (_≅_; Iso; IsIso; module ≅)
open import Categories.Morphism.Duality 𝒞 using (≅⇒op-≅)
open import Categories.Morphism.Reasoning 𝒞
open import Categories.Functor.Properties using ([_]-resp-≅)
open Shorthands
open BraidShorthands

private
  variable
    A B C D E F X Y Z : Obj

------------------------------------------------------------------------
-- `τ` — the trace of evaluation.  `τ^X_B : [ X , B ⊗₀ X ]₀ ⇒ B` is the trace,
-- over `X`, of `ev : [ X , B ⊗₀ X ]₀ ⊗₀ X ⇒ B ⊗₀ X`.  Tracing out `X` leaves a
-- map that reads a function and returns the `B` component of its self-application.

τ : [ X , B ⊗₀ X ]₀ ⇒ B
τ {X} {B} = trace {X = X} (eval {X} {B ⊗₀ X})

-- Its name, the ∗-autonomous transpose of the paper: `unit ⇒ [ [ X , B ⊗₀ X ]₀ , B ]₀`.
τ̂ : unit ⇒ [ [ X , B ⊗₀ X ]₀ , B ]₀
τ̂ = ⌜ τ ⌝

-- Applying a hom action `[ p , q ]₁` to `curry g` conjugates `g`: precompose the argument
-- with `p`, postcompose the result with `q`.  This is the one move every `φ` layer makes;
-- both the name-reindexing below and the `φ⁻¹` layers are instances.
hom-curry : {p : A ⇒ B} {q : X ⇒ Y} {g : C ⊗₀ B ⇒ X} → [ p , q ]₁ ∘ curry g ≈ curry (q ∘ g ∘ (id ⊗₁ p))
hom-curry {p = p} {q = q} {g = g} = uncurry-injective (begin
  uncurry ([ p , q ]₁ ∘ curry g)                 ≈⟨ uncurry-∘ ⟩
  (eval ∘ ([ p , q ]₁ ⊗₁ id)) ∘ (curry g ⊗₁ id)  ≈⟨ eval-comm {p = p} {q = q} ⟩∘⟨refl ⟩
  (q ∘ eval ∘ (id ⊗₁ p)) ∘ (curry g ⊗₁ id)       ≈⟨ assoc ⟩
  q ∘ (eval ∘ (id ⊗₁ p)) ∘ (curry g ⊗₁ id)       ≈⟨ refl⟩∘⟨ assoc ⟩
  q ∘ eval ∘ (id ⊗₁ p) ∘ (curry g ⊗₁ id)         ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ serialize₂₁ ⟩
  q ∘ eval ∘ (curry g ⊗₁ p)                       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ serialize₁₂ ⟩
  q ∘ eval ∘ (curry g ⊗₁ id) ∘ (id ⊗₁ p)         ≈⟨ refl⟩∘⟨ pullˡ eval-curry ⟩
  q ∘ g ∘ (id ⊗₁ p)                               ≈˘⟨ eval-curry ⟩
  uncurry (curry (q ∘ g ∘ (id ⊗₁ p)))            ∎)

-- The `q := id` reindexing on a `curry g`, the one every `φ⁻¹` layer uses.
hom-curryᵣ : {p : A ⇒ B} {g : C ⊗₀ B ⇒ X} → [ p , id ]₁ ∘ curry g ≈ curry (g ∘ (id ⊗₁ p))
hom-curryᵣ = hom-curry ○ curry-resp-≈ identityˡ

-- Tracing over the unit is conjugation by the right unitor: every `g : A ⊗₀ unit ⇒ B ⊗₀ unit`
-- is `(ρ⇒ ∘ g ∘ ρ⇐) ⊗₁ id` (the functor `- ⊗₀ unit ≅ Id` is full), so `vanishing₁` applies.
trace-unit : {g : A ⊗₀ unit ⇒ B ⊗₀ unit} → trace {X = unit} g ≈ ρ⇒ ∘ g ∘ ρ⇐
trace-unit {g = g} = begin
  trace g                       ≈⟨ trace⟨ ⟺ fold ⟩ ⟩
  trace ((ρ⇒ ∘ g ∘ ρ⇐) ⊗₁ id)   ≈⟨ vanishing₁ ⟩
  ρ⇒ ∘ g ∘ ρ⇐                   ∎
  where
    fold : (ρ⇒ ∘ g ∘ ρ⇐) ⊗₁ id ≈ g
    fold = begin
      (ρ⇒ ∘ g ∘ ρ⇐) ⊗₁ id                 ≈⟨ introʳ unitorʳ.isoˡ ⟩
      ((ρ⇒ ∘ g ∘ ρ⇐) ⊗₁ id) ∘ ρ⇐ ∘ ρ⇒     ≈⟨ pullˡ (⟺ unitorʳ-commute-to) ⟩
      (ρ⇐ ∘ ρ⇒ ∘ g ∘ ρ⇐) ∘ ρ⇒             ≈⟨ cancelˡ unitorʳ.isoˡ ⟩∘⟨refl ⟩
      (g ∘ ρ⇐) ∘ ρ⇒                       ≈⟨ cancelʳ unitorʳ.isoˡ ⟩
      g                                   ∎

-- Tracing evaluation at the unit collapses (vanishing) to `ρ⇒ ∘ unit-hom⇐`.
τ-unit : τ {unit} {B} ≈ ρ⇒ ∘ unit-hom⇐
τ-unit = trace-unit

-- Lemma 3.1.  `τ` is dinatural in `X`.  Reindexing the *codomain* copy of `X` along
-- `g` (post-composing `id ⊗₁ g` inside the function) agrees with reindexing the
-- *argument* copy (pre-composing the function with `g`).  The heart is the trace's
-- `slide`; evaluation's naturality on each side turns the two hom-functor actions into
-- the whiskered `id ⊗₁ g` that `slide` moves across the trace.  This is what makes
-- `name τ` extraordinarily natural in `X`.
τ-dinatural : {g : X ⇒ Y} → τ {Y} {B} ∘ [ id , id ⊗₁ g ]₁ ≈ τ {X} {B} ∘ [ g , id ]₁
τ-dinatural {g = g} = begin
  τ ∘ [ id , id ⊗₁ g ]₁                   ≈˘⟨ tightenᵣ ⟩
  trace (eval ∘ ([ id , id ⊗₁ g ]₁ ⊗₁ id))  ≈⟨ trace⟨ eval-comm-cod ⟩ ⟩
  trace ((id ⊗₁ g) ∘ eval)                   ≈˘⟨ slide ⟩
  trace (eval ∘ (id ⊗₁ g))                   ≈˘⟨ trace⟨ eval-comm-dom ⟩ ⟩
  trace (eval ∘ ([ g , id ]₁ ⊗₁ id))         ≈⟨ tightenᵣ ⟩
  τ ∘ [ g , id ]₁                          ∎

-- Lemma 3.1 in its enriched form.  The two internal functions are parameters:
-- first compose them and trace over `X`, or evaluate the `Y`-function, feed its
-- `X` output through the other function, and trace over `Y`.
τ-extra :
  {X Y B : Obj} →
    τ {X} {B} ∘ internal-∘ {Y} {B ⊗₀ X} {X}
  ≈ τ {Y} {B} ∘ curry
      ((id ⊗₁ eval {X} {Y}) ∘ (id ⊗₁ σ⇒) ∘ α⇒
        ∘ (eval {Y} {B ⊗₀ X} ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒)
τ-extra {X} {Y} {B} = begin
  τ ∘ internal-∘                        ≈˘⟨ tightenᵣ ⟩
  trace (eval ∘ (internal-∘ ⊗₁ id))      ≈⟨ trace⟨ eval-internal-∘ ⟩ ⟩
  trace left                             ≈˘⟨ trace⟨ inner-trace ⟩ ⟩
  trace inside                           ≈⟨ vanish ⟩
  trace around                           ≈⟨ slide-parameters ⟩
  trace right                            ≈˘⟨ trace⟨ eval-curry ⟩ ⟩
  trace (eval ∘ (curry right ⊗₁ id))     ≈⟨ tightenᵣ ⟩
  τ ∘ curry right                        ≈⟨ refl⟩∘⟨ curry-resp-≈ right-expand ⟩
  τ ∘ curry
    ((id ⊗₁ eval {X} {Y}) ∘ (id ⊗₁ σ⇒) ∘ α⇒
      ∘ (eval {Y} {B ⊗₀ X} ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒)  ∎
  where
    swap : {A C D : Obj} → (A ⊗₀ C) ⊗₀ D ⇒ (A ⊗₀ D) ⊗₀ C
    swap = α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒

    left : ([ Y , B ⊗₀ X ]₀ ⊗₀ [ X , Y ]₀) ⊗₀ X ⇒ B ⊗₀ X
    left = eval ∘ (id ⊗₁ eval) ∘ α⇒

    forward : ([ Y , B ⊗₀ X ]₀ ⊗₀ [ X , Y ]₀) ⊗₀ Y ⇒ B ⊗₀ (X ⊗₀ [ X , Y ]₀)
    forward = α⇒ ∘ (eval ⊗₁ id) ∘ swap

    around :
      ([ Y , B ⊗₀ X ]₀ ⊗₀ [ X , Y ]₀) ⊗₀ (X ⊗₀ [ X , Y ]₀) ⇒
      B ⊗₀ (X ⊗₀ [ X , Y ]₀)
    around = forward ∘ (id ⊗₁ (eval ∘ σ⇒))

    right : ([ Y , B ⊗₀ X ]₀ ⊗₀ [ X , Y ]₀) ⊗₀ Y ⇒ B ⊗₀ Y
    right = (id ⊗₁ (eval ∘ σ⇒)) ∘ forward

    right-expand : right ≈
          (id ⊗₁ eval {X} {Y}) ∘ (id ⊗₁ σ⇒) ∘ α⇒
          ∘ (eval {Y} {B ⊗₀ X} ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒
    right-expand = begin
      (id ⊗₁ (eval ∘ σ⇒)) ∘ forward
        ≈⟨ split₂ˡ ⟩∘⟨refl ⟩
      ((id ⊗₁ eval) ∘ (id ⊗₁ σ⇒)) ∘ forward
        ≈⟨ assoc ⟩
      (id ⊗₁ eval) ∘ (id ⊗₁ σ⇒) ∘ α⇒
        ∘ (eval ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒  ∎

    loop :
      (([ Y , B ⊗₀ X ]₀ ⊗₀ [ X , Y ]₀) ⊗₀ X) ⊗₀ [ X , Y ]₀ ⇒
      (([ Y , B ⊗₀ X ]₀ ⊗₀ [ X , Y ]₀) ⊗₀ X) ⊗₀ [ X , Y ]₀
    loop = (swap ⊗₁ id) ∘ swap ∘ (swap ⊗₁ id)

    swap-cancel : {A C D : Obj} → swap {A} {D} {C} ∘ swap {A} {C} {D} ≈ id
    swap-cancel = begin
      (α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒
        ≈⟨ pullʳ (cancelInner associator.isoʳ) ⟩
      α⇐ ∘ (id ⊗₁ σ⇒) ∘ (id ⊗₁ σ⇒) ∘ α⇒
        ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
      α⇐ ∘ (id ⊗₁ (σ⇒ ∘ σ⇒)) ∘ α⇒
        ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ commutative) ⟩∘⟨refl ⟩
      α⇐ ∘ (id ⊗₁ id) ∘ α⇒
        ≈⟨ elim-center ⊗.identity ○ associator.isoˡ ⟩
      id  ∎

    swap-natural :
      {A A′ C C′ D D′ : Obj} {f : A ⇒ A′} {g : C ⇒ C′} {h : D ⇒ D′} →
      swap ∘ ((f ⊗₁ g) ⊗₁ h) ≈ ((f ⊗₁ h) ⊗₁ g) ∘ swap
    swap-natural {f = f} {g} {h} = begin
      (α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒) ∘ ((f ⊗₁ g) ⊗₁ h)
        ≈⟨ pullʳ (pullʳ assoc-commute-from) ⟩
      α⇐ ∘ (id ⊗₁ σ⇒) ∘ (f ⊗₁ (g ⊗₁ h)) ∘ α⇒
        ≈⟨ refl⟩∘⟨ extendʳ (parallel id-comm-sym σ⇒-comm) ⟩
      α⇐ ∘ (f ⊗₁ (h ⊗₁ g)) ∘ (id ⊗₁ σ⇒) ∘ α⇒
        ≈⟨ extendʳ assoc-commute-to ⟩
      ((f ⊗₁ h) ⊗₁ g) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒  ∎

    loop-trace : trace loop ≈ id
    loop-trace = begin
      trace ((swap ⊗₁ id) ∘ swap ∘ (swap ⊗₁ id))  ≈⟨ tightenₗ ⟩
      swap ∘ trace (swap ∘ (swap ⊗₁ id))           ≈⟨ refl⟩∘⟨ tightenᵣ ⟩
      swap ∘ trace swap ∘ swap                     ≈⟨ refl⟩∘⟨ superposing ⟩∘⟨refl ⟩
      swap ∘ (id ⊗₁ trace σ⇒) ∘ swap               ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ yanking) ⟩∘⟨refl ⟩
      swap ∘ (id ⊗₁ id) ∘ swap                     ≈⟨ refl⟩∘⟨ ⊗.identity ⟩∘⟨refl ⟩
      swap ∘ id ∘ swap                              ≈⟨ refl⟩∘⟨ identityˡ ⟩
      swap ∘ swap                                   ≈⟨ swap-cancel ⟩
      id                                            ∎

    α-swap : {A C D : Obj} → α⇒ ∘ swap {A} {C} {D} ≈ (id ⊗₁ σ⇒) ∘ α⇒
    α-swap = begin
      α⇒ ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒  ≈⟨ pullˡ associator.isoʳ ○ identityˡ ⟩
      (id ⊗₁ σ⇒) ∘ α⇒             ∎

    lift₂ : {P C D E F : Obj} → C ⊗₀ D ⇒ E ⊗₀ F → (P ⊗₀ C) ⊗₀ D ⇒ (P ⊗₀ E) ⊗₀ F
    lift₂ h = α⇐ ∘ (id ⊗₁ h) ∘ α⇒

    lift₂-resp-≈ :
      {P C D E F : Obj} {h k : C ⊗₀ D ⇒ E ⊗₀ F} → h ≈ k → lift₂ {P} h ≈ lift₂ k
    lift₂-resp-≈ h≈k = refl⟩∘⟨ (refl⟩⊗⟨ h≈k) ⟩∘⟨refl

    lift₂-∘ :
      {P C D E F G H : Obj} {h : E ⊗₀ F ⇒ G ⊗₀ H} {k : C ⊗₀ D ⇒ E ⊗₀ F} →
      lift₂ {P} h ∘ lift₂ {P} k ≈ lift₂ {P} (h ∘ k)
    lift₂-∘ {h = h} {k} = begin
      (α⇐ ∘ (id ⊗₁ h) ∘ α⇒) ∘ α⇐ ∘ (id ⊗₁ k) ∘ α⇒
        ≈⟨ center (cancelʳ associator.isoʳ) ⟩
      α⇐ ∘ (id ⊗₁ h) ∘ (id ⊗₁ k) ∘ α⇒       ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
      α⇐ ∘ (id ⊗₁ (h ∘ k)) ∘ α⇒             ∎

    lift₂-factor :
      {P C D E F G H : Obj} {h : E ⊗₀ F ⇒ G ⊗₀ H} {k : C ⊗₀ D ⇒ E ⊗₀ F}
      {h′ : (P ⊗₀ E) ⊗₀ F ⇒ (P ⊗₀ G) ⊗₀ H} →
      lift₂ {P} h ≈ h′ → lift₂ {P} (h ∘ k) ≈ h′ ∘ lift₂ {P} k
    lift₂-factor h≈h′ = ⟺ lift₂-∘ ○ (h≈h′ ⟩∘⟨refl)

    lift₂-eval :
      {P C D E F : Obj} {h : C ⊗₀ D ⇒ E ⊗₀ F}
      {k : (P ⊗₀ C) ⊗₀ D ⇒ (P ⊗₀ E) ⊗₀ F} →
      (id ⊗₁ h) ∘ α⇒ ≈ α⇒ ∘ k → lift₂ h ≈ k
    lift₂-eval h-past-α = (refl⟩∘⟨ h-past-α) ○ cancelˡ associator.isoˡ

    lift₂-⊗id :
      {P C D E : Obj} {f : C ⇒ E} → lift₂ {P} (f ⊗₁ id {D}) ≈ (id ⊗₁ f) ⊗₁ id
    lift₂-⊗id = lift₂-eval (⟺ assoc-commute-from)

    lift₂-id⊗ :
      {P C D E : Obj} {f : D ⇒ E} → lift₂ {P} (id {C} ⊗₁ f) ≈ id ⊗₁ f
    lift₂-id⊗ = lift₂-eval (⟺ α⇒-id⊗-commute)

    lift₂-α⇒ : {S C D E : Obj} → lift₂ {S} (α⇒ {C} {D} {E}) ≈ α⇒ ∘ (α⇐ ⊗₁ id)
    lift₂-α⇒ = ⟺ assoc-from-coherence

    lift₂-factor-α⇒ :
      {P Q C D E S : Obj} {k : P ⊗₀ Q ⇒ (C ⊗₀ D) ⊗₀ E} →
      lift₂ {S} (α⇒ ∘ k) ≈ (α⇒ ∘ (α⇐ ⊗₁ id)) ∘ lift₂ {S} k
    lift₂-factor-α⇒ = lift₂-factor lift₂-α⇒

    lift₂-α⇐ : {S C D E : Obj} → lift₂ {S} (α⇐ {C} {D} {E}) ≈ (α⇒ ⊗₁ id) ∘ α⇐
    lift₂-α⇐ = lift₂-eval assoc-to-coherence

    lift₂-α⇐-cancel : {S C D E : Obj} → lift₂ {S} (α⇐ {C} {D} {E}) ∘ α⇒ ≈ α⇒ ⊗₁ id
    lift₂-α⇐-cancel = (lift₂-α⇐ ⟩∘⟨refl) ○ cancelʳ associator.isoˡ

    braid-loop-collapse :
        (id {C} ⊗₁ σ⇒ {D} {E}) ∘ α⇒ ∘ (σ⇒ {D} {C} ⊗₁ id) ∘ α⇐
      ≈ α⇒ ∘ σ⇒
    braid-loop-collapse = begin
      (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐       ≈⟨ assoc²εβ ⟩
      ((id ⊗₁ σ⇒) ∘ (α⇒ ∘ (σ⇒ ⊗₁ id))) ∘ α⇐   ≈⟨ hexagon₁ ⟩∘⟨refl ⟩
      (α⇒ ∘ (σ⇒ ∘ α⇒)) ∘ α⇐                   ≈⟨ pullʳ (cancelʳ associator.isoʳ) ⟩
      α⇒ ∘ σ⇒                                 ∎

    swap-fuse : swap ∘ α⇒ ≈ (α⇒ ⊗₁ id) ∘ swap ∘ (swap ⊗₁ id)
    swap-fuse = begin
      lift₂ σ⇒ ∘ α⇒
        ≈˘⟨ lift₂-resp-≈ (cancelˡ associator.isoˡ) ⟩∘⟨refl ⟩
      lift₂ (α⇐ ∘ α⇒ ∘ σ⇒) ∘ α⇒
        ≈˘⟨ lift₂-resp-≈ (refl⟩∘⟨ braid-loop-collapse) ⟩∘⟨refl ⟩
      lift₂ (α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐) ∘ α⇒
        ≈⟨ pushˡ (lift₂-factor lift₂-α⇐) ⟩
      ((α⇒ ⊗₁ id) ∘ α⇐) ∘ lift₂ ((id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐) ∘ α⇒
        ≈⟨ refl⟩∘⟨ pushˡ (lift₂-factor lift₂-id⊗) ⟩
      ((α⇒ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ σ⇒) ∘ lift₂ (α⇒ ∘ (σ⇒ ⊗₁ id) ∘ α⇐) ∘ α⇒
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ lift₂-factor-α⇒ ⟩
      ((α⇒ ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ σ⇒) ∘ (α⇒ ∘ (α⇐ ⊗₁ id))
        ∘ lift₂ ((σ⇒ ⊗₁ id) ∘ α⇐) ∘ α⇒
        ≈⟨ assoc ⟩
      (α⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ (α⇒ ∘ (α⇐ ⊗₁ id))
        ∘ lift₂ ((σ⇒ ⊗₁ id) ∘ α⇐) ∘ α⇒
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
      (α⇒ ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (α⇐ ⊗₁ id)
        ∘ lift₂ ((σ⇒ ⊗₁ id) ∘ α⇐) ∘ α⇒
        ≈˘⟨ refl⟩∘⟨ assoc²βε ⟩
      (α⇒ ⊗₁ id) ∘ swap ∘ (α⇐ ⊗₁ id) ∘ lift₂ ((σ⇒ ⊗₁ id) ∘ α⇐) ∘ α⇒
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (lift₂-factor lift₂-⊗id) ⟩
      (α⇒ ⊗₁ id) ∘ swap ∘ (α⇐ ⊗₁ id) ∘ ((id ⊗₁ σ⇒) ⊗₁ id)
        ∘ lift₂ α⇐ ∘ α⇒
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ lift₂-α⇐-cancel ⟩
      (α⇒ ⊗₁ id) ∘ swap ∘ (α⇐ ⊗₁ id) ∘ ((id ⊗₁ σ⇒) ⊗₁ id) ∘ (α⇒ ⊗₁ id)
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ split₁³ ⟩
      (α⇒ ⊗₁ id) ∘ swap ∘ (swap ⊗₁ id)  ∎

    loop-normal :
        (α⇒ ⊗₁ id) ∘ loop
      ≈ swap ∘ (id ⊗₁ σ⇒) ∘ α⇒
    loop-normal = begin
      (α⇒ ⊗₁ id) ∘ (swap ⊗₁ id) ∘ swap ∘ (swap ⊗₁ id)
        ≈⟨ pullˡ merge₁ˡ ⟩
      ((α⇒ ∘ swap) ⊗₁ id) ∘ swap ∘ (swap ⊗₁ id)
        ≈⟨ (α-swap ⟩⊗⟨refl) ⟩∘⟨refl ⟩
      (((id ⊗₁ σ⇒) ∘ α⇒) ⊗₁ id) ∘ swap ∘ (swap ⊗₁ id)
        ≈⟨ pushˡ split₁ˡ ⟩
      ((id ⊗₁ σ⇒) ⊗₁ id) ∘ (α⇒ ⊗₁ id) ∘ swap ∘ (swap ⊗₁ id)
        ≈˘⟨ refl⟩∘⟨ swap-fuse ⟩
      ((id ⊗₁ σ⇒) ⊗₁ id) ∘ swap ∘ α⇒
        ≈⟨ sym-assoc ⟩
      (((id ⊗₁ σ⇒) ⊗₁ id) ∘ swap) ∘ α⇒
        ≈˘⟨ swap-natural ⟩∘⟨refl ⟩
      (swap ∘ ((id ⊗₁ id) ⊗₁ σ⇒)) ∘ α⇒
        ≈⟨ assoc ⟩
      swap ∘ ((id ⊗₁ id) ⊗₁ σ⇒) ∘ α⇒
        ≈⟨ refl⟩∘⟨ (⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl ⟩
      swap ∘ (id ⊗₁ σ⇒) ∘ α⇒  ∎

    loop-coherence :
        swap ∘ (id ⊗₁ σ⇒) ∘ α⇒
      ≈ (α⇒ ⊗₁ id) ∘ loop
    loop-coherence = ⟺ loop-normal

    swap-eval :
        swap ∘ ((id {[ Y , B ⊗₀ X ]₀} ⊗₁ id) ⊗₁ eval {X} {Y})
      ≈ ((id ⊗₁ eval) ⊗₁ id) ∘ swap
    swap-eval = swap-natural

    split-eval :
        (id ⊗₁ (eval {X} {Y} ∘ σ⇒)) ∘ α⇒
      ≈ (id ⊗₁ eval) ∘ (id ⊗₁ σ⇒) ∘ α⇒
    split-eval = pushˡ split₂ˡ

    around-expand :
      around ≈ α⇒ ∘ (eval ⊗₁ id) ∘ swap ∘ (id ⊗₁ (eval ∘ σ⇒))
    around-expand = assoc²βε

    factor-head :
        α⇐ ∘ around ∘ α⇒
      ≈ (eval ⊗₁ id) ∘ swap ∘ (id ⊗₁ eval) ∘ (id ⊗₁ σ⇒) ∘ α⇒
    factor-head = begin
      α⇐ ∘ around ∘ α⇒
        ≈⟨ refl⟩∘⟨ (around-expand ⟩∘⟨refl) ⟩
      α⇐ ∘ (α⇒ ∘ (eval ⊗₁ id) ∘ swap ∘ (id ⊗₁ (eval ∘ σ⇒))) ∘ α⇒
        ≈⟨ refl⟩∘⟨ ⟺ reassoc-tail₅ ⟩
      α⇐ ∘ α⇒ ∘ (eval ⊗₁ id) ∘ swap ∘ (id ⊗₁ (eval ∘ σ⇒)) ∘ α⇒
        ≈⟨ pullˡ associator.isoˡ ○ identityˡ ⟩
      (eval ⊗₁ id) ∘ swap ∘ (id ⊗₁ (eval ∘ σ⇒)) ∘ α⇒
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ split-eval ⟩
      (eval ⊗₁ id) ∘ swap ∘ (id ⊗₁ eval) ∘ (id ⊗₁ σ⇒) ∘ α⇒  ∎

    factor : α⇐ ∘ around ∘ α⇒ ≈ (left ⊗₁ id) ∘ loop
    factor = begin
      α⇐ ∘ around ∘ α⇒
        ≈⟨ factor-head ⟩
      (eval ⊗₁ id) ∘ swap ∘ (id ⊗₁ eval) ∘ (id ⊗₁ σ⇒) ∘ α⇒
        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ ((⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl) ⟩
      (eval ⊗₁ id) ∘ swap ∘ ((id ⊗₁ id) ⊗₁ eval) ∘ (id ⊗₁ σ⇒) ∘ α⇒
        ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      (eval ⊗₁ id) ∘ (swap ∘ ((id ⊗₁ id) ⊗₁ eval)) ∘ (id ⊗₁ σ⇒) ∘ α⇒
        ≈⟨ refl⟩∘⟨ swap-eval ⟩∘⟨refl ⟩
      (eval ⊗₁ id) ∘ (((id ⊗₁ eval) ⊗₁ id) ∘ swap) ∘ (id ⊗₁ σ⇒) ∘ α⇒
        ≈⟨ refl⟩∘⟨ assoc ⟩
      (eval ⊗₁ id) ∘ ((id ⊗₁ eval) ⊗₁ id) ∘ swap ∘ (id ⊗₁ σ⇒) ∘ α⇒
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ loop-coherence ⟩
      (eval ⊗₁ id) ∘ ((id ⊗₁ eval) ⊗₁ id) ∘ (α⇒ ⊗₁ id) ∘ loop
        ≈⟨ assoc²εβ ⟩
      ((eval ⊗₁ id) ∘ ((id ⊗₁ eval) ⊗₁ id) ∘ (α⇒ ⊗₁ id)) ∘ loop
        ≈⟨ merge₁³ ⟩∘⟨refl ⟩
      (left ⊗₁ id) ∘ loop  ∎

    inside : ([ Y , B ⊗₀ X ]₀ ⊗₀ [ X , Y ]₀) ⊗₀ X ⇒ B ⊗₀ X
    inside = trace (α⇐ ∘ around ∘ α⇒)

    vanish : trace inside ≈ trace around
    vanish = vanishing₂

    slide-parameters : trace around ≈ trace right
    slide-parameters = slide

    inner-trace : inside ≈ left
    inner-trace = begin
      trace (α⇐ ∘ around ∘ α⇒)  ≈⟨ trace⟨ factor ⟩ ⟩
      trace ((left ⊗₁ id) ∘ loop)  ≈⟨ tightenₗ ⟩
      left ∘ trace loop             ≈⟨ refl⟩∘⟨ loop-trace ⟩
      left ∘ id                     ≈⟨ identityʳ ⟩
      left                          ∎

------------------------------------------------------------------------
-- Symmetric-closed isomorphisms used to assemble `φ`.

-- The braiding, as an isomorphism.
⊗-comm-≅ : (A ⊗₀ B) ≅ (B ⊗₀ A)
⊗-comm-≅ = record
  { from = σ⇒
  ; to   = σ⇒
  ; iso  = record { isoˡ = commutative ; isoʳ = commutative }
  }

-- Swap-currying: a function of `A ⊗₀ B` is a function of `B` returning a function of `A`.
-- Compose the currying isomorphism with the internal hom of the braiding.
swap-curry-≅ : [ A ⊗₀ B , C ]₀ ≅ [ B , [ A , C ]₀ ]₀
swap-curry-≅ {A} {B} {C} = ≅.trans ([ [-, C ] ]-resp-≅ (≅⇒op-≅ ⊗-comm-≅)) curry₂-iso

-- Naturality of swap-currying (brick 3 of `φ`): contravariant in `A`, `B`, covariant in `C`.
-- Post-composing `curry₂`'s square onto the braiding turns `[ f ⊗₁ g , h ]₁` on the source
-- into the swapped `[ g , [ f , h ]₁ ]₁` on the target, the two bridged by `σ⇒-comm`.
swap-curry-natural : {f : X ⇒ A} {g : Y ⇒ B} {h : C ⇒ Z} →
    [ g , [ f , h ]₁ ]₁ ∘ (curry₂ ∘ [ σ⇒ , id ]₁)
  ≈ (curry₂ ∘ [ σ⇒ , id ]₁) ∘ [ f ⊗₁ g , h ]₁
swap-curry-natural {f = f} {g = g} {h = h} = begin
  [ g , [ f , h ]₁ ]₁ ∘ (curry₂ ∘ [ σ⇒ , id ]₁)  ≈⟨ pullˡ curry₂-natural ⟩
  (curry₂ ∘ [ g ⊗₁ f , h ]₁) ∘ [ σ⇒ , id ]₁       ≈⟨ assoc ⟩
  curry₂ ∘ [ g ⊗₁ f , h ]₁ ∘ [ σ⇒ , id ]₁         ≈˘⟨ refl⟩∘⟨ [-,-].homomorphism ⟩
  curry₂ ∘ [ σ⇒ ∘ (g ⊗₁ f) , h ∘ id ]₁            ≈⟨ refl⟩∘⟨ [-,-].F-resp-≈ (σ⇒-comm , id-comm) ⟩
  curry₂ ∘ [ (f ⊗₁ g) ∘ σ⇒ , id ∘ h ]₁            ≈⟨ refl⟩∘⟨ [-,-].homomorphism ⟩
  curry₂ ∘ [ σ⇒ , id ]₁ ∘ [ f ⊗₁ g , h ]₁         ≈˘⟨ assoc ⟩
  (curry₂ ∘ [ σ⇒ , id ]₁) ∘ [ f ⊗₁ g , h ]₁       ∎

-- Composition of internal-hom actions (contravariant first slot, covariant second):
-- the `[-,-]` bifunctor's homomorphism law, oriented for rewriting.
hom-∘ : {a : C ⇒ B} {c : B ⇒ A} {b : Y ⇒ Z} {d : X ⇒ Y} →
  [ a , b ]₁ ∘ [ c , d ]₁ ≈ [ c ∘ a , b ∘ d ]₁
hom-∘ = ⟺ [-,-].homomorphism

-- The covariant slots both `id`: their composite is again `id`, kept normalized.
hom-∘ᵣ : {a : C ⇒ B} {c : B ⇒ A} → [ a , id {X} ]₁ ∘ [ c , id ]₁ ≈ [ c ∘ a , id ]₁
hom-∘ᵣ = hom-∘ ○ [-,-].F-resp-≈ (Equiv.refl , identity²)

-- Associativity of internal composition, `h ∘ (g ∘ f) = (h ∘ g) ∘ f` internalized.  Proved by
-- uncurrying to three nested `eval`s on either side; the two bracketings differ by one `pentagon`.
internal-∘-assoc :
  {A B C D : Obj} →
    internal-∘ {B} {D} {A} ∘ (internal-∘ {C} {D} {B} ⊗₁ id)
  ≈ internal-∘ {C} {D} {A} ∘ (id ⊗₁ internal-∘ {B} {C} {A}) ∘ α⇒
internal-∘-assoc {A} {B} {C} {D} = uncurry-injective (begin
  uncurry (internal-∘ ∘ (internal-∘ ⊗₁ id))
    ≈⟨ uncurry-∘ ⟩
  uncurry internal-∘ ∘ ((internal-∘ ⊗₁ id) ⊗₁ id)
    ≈⟨ eval-internal-∘ ⟩∘⟨refl ⟩
  (eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ ((internal-∘ ⊗₁ id) ⊗₁ id)
    ≈⟨ assoc ⟩
  eval ∘ ((id ⊗₁ eval) ∘ α⇒) ∘ ((internal-∘ ⊗₁ id) ⊗₁ id)
    ≈⟨ refl⟩∘⟨ assoc ⟩
  eval ∘ (id ⊗₁ eval) ∘ α⇒ ∘ ((internal-∘ ⊗₁ id) ⊗₁ id)
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-commute-from ⟩
  eval ∘ (id ⊗₁ eval) ∘ (internal-∘ ⊗₁ (id ⊗₁ id)) ∘ α⇒
    ≈⟨ refl⟩∘⟨ pullˡ ev-swap ⟩
  eval ∘ ((internal-∘ ⊗₁ id) ∘ (id ⊗₁ eval)) ∘ α⇒
    ≈⟨ refl⟩∘⟨ assoc ⟩
  eval ∘ (internal-∘ ⊗₁ id) ∘ (id ⊗₁ eval) ∘ α⇒
    ≈⟨ pullˡ eval-internal-∘ ⟩
  (eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ (id ⊗₁ eval) ∘ α⇒
    ≈⟨ assoc ⟩
  eval ∘ ((id ⊗₁ eval) ∘ α⇒) ∘ (id ⊗₁ eval) ∘ α⇒
    ≈⟨ refl⟩∘⟨ assoc ⟩
  eval ∘ (id ⊗₁ eval) ∘ α⇒ ∘ (id ⊗₁ eval) ∘ α⇒
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ α⇒-id⊗-commute ⟩
  eval ∘ (id ⊗₁ eval) ∘ ((id ⊗₁ (id ⊗₁ eval)) ∘ α⇒) ∘ α⇒
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
  eval ∘ (id ⊗₁ eval) ∘ (id ⊗₁ (id ⊗₁ eval)) ∘ α⇒ ∘ α⇒
    ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pentagon ⟩
  eval ∘ (id ⊗₁ eval) ∘ (id ⊗₁ (id ⊗₁ eval)) ∘ (id ⊗₁ α⇒) ∘ α⇒ ∘ (α⇒ ⊗₁ id)
    ≈˘⟨ refl⟩∘⟨ ((split3 ⟩∘⟨refl) ○ assoc ○ (refl⟩∘⟨ assoc)) ⟩
  eval ∘ (id ⊗₁ (eval ∘ (id ⊗₁ eval) ∘ α⇒)) ∘ α⇒ ∘ (α⇒ ⊗₁ id)
    ≈˘⟨ refl⟩∘⟨ (refl⟩⊗⟨ eval-internal-∘) ⟩∘⟨refl ⟩
  eval ∘ (id ⊗₁ uncurry (internal-∘ {B} {C} {A})) ∘ α⇒ ∘ (α⇒ ⊗₁ id)
    ≈˘⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
  eval ∘ (id ⊗₁ eval) ∘ (id ⊗₁ (internal-∘ {B} {C} {A} ⊗₁ id)) ∘ α⇒ ∘ (α⇒ ⊗₁ id)
    ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ (pullˡ assoc-commute-from ○ assoc) ⟩
  eval ∘ (id ⊗₁ eval) ∘ α⇒ ∘ ((id ⊗₁ internal-∘ {B} {C} {A}) ⊗₁ id) ∘ (α⇒ ⊗₁ id)
    ≈˘⟨ assoc ○ (refl⟩∘⟨ assoc) ⟩
  (eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ ((id ⊗₁ internal-∘ {B} {C} {A}) ⊗₁ id) ∘ (α⇒ ⊗₁ id)
    ≈˘⟨ (eval-internal-∘ ⟩∘⟨refl) ○ (refl⟩∘⟨ split₁ˡ) ⟩
  uncurry (internal-∘ {C} {D} {A}) ∘ (((id ⊗₁ internal-∘ {B} {C} {A}) ∘ α⇒) ⊗₁ id)
    ≈˘⟨ uncurry-∘ ⟩
  uncurry (internal-∘ ∘ (id ⊗₁ internal-∘) ∘ α⇒) ∎)
  where
    -- Swap the whiskered `internal-∘` past `eval` on the other factor.
    ev-swap : (id ⊗₁ eval {A} {B}) ∘ (internal-∘ {C} {D} {B} ⊗₁ (id ⊗₁ id))
            ≈ (internal-∘ {C} {D} {B} ⊗₁ id) ∘ (id ⊗₁ eval {A} {B})
    ev-swap = begin
      (id ⊗₁ eval) ∘ (internal-∘ ⊗₁ (id ⊗₁ id))  ≈⟨ ⟺ ⊗.homomorphism ⟩
      (id ∘ internal-∘) ⊗₁ (eval ∘ (id ⊗₁ id))    ≈⟨ identityˡ ⟩⊗⟨ elimʳ ⊗.identity ⟩
      internal-∘ ⊗₁ eval                            ≈⟨ serialize₁₂ ⟩
      (internal-∘ ⊗₁ id) ∘ (id ⊗₁ eval)            ∎
    -- Distribute the whisker over the three-fold composite.
    split3 : id ⊗₁ (eval ∘ (id ⊗₁ eval) ∘ α⇒)
           ≈ (id ⊗₁ eval) ∘ (id ⊗₁ (id ⊗₁ eval)) ∘ (id ⊗₁ α⇒)
    split3 = begin
      id ⊗₁ (eval ∘ (id ⊗₁ eval) ∘ α⇒)                   ≈⟨ split₂ˡ ⟩
      (id ⊗₁ eval) ∘ (id ⊗₁ ((id ⊗₁ eval) ∘ α⇒))         ≈⟨ refl⟩∘⟨ split₂ˡ ⟩
      (id ⊗₁ eval) ∘ (id ⊗₁ (id ⊗₁ eval)) ∘ (id ⊗₁ α⇒)  ∎

-- Lift an inner naturality square through dualization `[ - , D ]` (contravariant first
-- slot): a square `b ∘ p ≈ q ∘ b′` becomes the dual square on the hom objects.
dual-push : {b : A ⇒ B} {b′ : C ⇒ Z} {p : C ⇒ A} {q : Z ⇒ B} →
    b ∘ p ≈ q ∘ b′ →
    [ p , id {X} ]₁ ∘ [ b , id ]₁ ≈ [ b′ , id ]₁ ∘ [ q , id ]₁
dual-push {b = b} {b′} {p} {q} sq = begin
  [ p , id ]₁ ∘ [ b , id ]₁     ≈⟨ hom-∘ ⟩
  [ b ∘ p , id ∘ id ]₁          ≈⟨ [-,-].F-resp-≈ (sq , Equiv.refl) ⟩
  [ q ∘ b′ , id ∘ id ]₁         ≈˘⟨ hom-∘ ⟩
  [ b′ , id ]₁ ∘ [ q , id ]₁    ∎

-- Lift an inner naturality square through the covariant hom `[ - ,= ]` (second slot),
-- keeping the fixed first-slot map `r`.  Oriented to match the layer commutes below.
homˡ-push : {r : A ⇒ B} {v : C ⇒ Z} {v′ : X ⇒ Y} {c : C ⇒ X} {c′ : Z ⇒ Y} →
    v′ ∘ c ≈ c′ ∘ v →
    [ r , c′ ]₁ ∘ [ id {B} , v ]₁ ≈ [ id {A} , v′ ]₁ ∘ [ r , c ]₁
homˡ-push {r = r} {v} {v′} {c} {c′} sq = begin
  [ r , c′ ]₁ ∘ [ id , v ]₁     ≈⟨ hom-∘ ⟩
  [ id ∘ r , c′ ∘ v ]₁          ≈˘⟨ [-,-].F-resp-≈ (id-comm , sq) ⟩
  [ r ∘ id , v′ ∘ c ]₁          ≈˘⟨ hom-∘ ⟩
  [ id , v′ ]₁ ∘ [ r , c ]₁     ∎

-- Maps on independent hom slots commute: `[ id , k ]₁` past `[ g , id ]₁`.
hom-interchange : {g : A ⇒ B} {k : X ⇒ Y} → [ id , k ]₁ ∘ [ g , id ]₁ ≈ [ g , id ]₁ ∘ [ id , k ]₁
hom-interchange {g = g} {k = k} = begin
  [ id , k ]₁ ∘ [ g , id ]₁    ≈⟨ hom-∘ ⟩
  [ g ∘ id , k ∘ id ]₁         ≈⟨ [-,-].F-resp-≈ (id-comm , id-comm) ⟩
  [ id ∘ g , id ∘ k ]₁         ≈˘⟨ hom-∘ ⟩
  [ g , id ]₁ ∘ [ id , k ]₁    ∎

-- Lift an isomorphism through the covariant hom functor `[ D ,-]`.
homˡ : (D : Obj) {A B : Obj} → A ≅ B → [ D , A ]₀ ≅ [ D , B ]₀
homˡ D = [ [ D ,-] ]-resp-≅

------------------------------------------------------------------------
-- Dualizing object (Barr, 1979).  The canonical map `δ : A ⇒ [ [ A , D ]₀ , D ]₀`
-- names a value and hands it to its own continuation.  `D` is *dualizing* when `δ` is
-- invertible at every `A`, i.e. `A` is recovered from its double dual `[ [ A , D ]₀ , D ]₀`.

δ : (D : Obj) → A ⇒ [ [ A , D ]₀ , D ]₀
δ D = curry (eval ∘ σ⇒)

-- `δ` is natural in `A`: it is a transformation `Id ⟹ (- ⊗₀ D-dual double dual)`.  The
-- proof uncurries and reduces both sides to `ev ∘ σ⇒` bridged by braiding naturality,
-- turning each hom-functor action into an argument-side whisker via `ev-comm-dom`.
δ-natural : {D : Obj} {h : A ⇒ B} → [ [ h , id ]₁ , id ]₁ ∘ δ D ≈ δ {B} D ∘ h
δ-natural {D = D} {h = h} = uncurry-injective (begin
  eval ∘ (([ [ h , id ]₁ , id ]₁ ∘ δ D) ⊗₁ id)        ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
  eval ∘ ([ [ h , id ]₁ , id ]₁ ⊗₁ id) ∘ (δ D ⊗₁ id)  ≈⟨ pullˡ eval-comm-dom ⟩
  (eval ∘ (id ⊗₁ [ h , id ]₁)) ∘ (δ D ⊗₁ id)          ≈⟨ assoc ⟩
  eval ∘ (id ⊗₁ [ h , id ]₁) ∘ (δ D ⊗₁ id)            ≈˘⟨ refl⟩∘⟨ whisker-comm ⟩
  eval ∘ (δ D ⊗₁ id) ∘ (id ⊗₁ [ h , id ]₁)            ≈⟨ pullˡ eval-curry ⟩
  (eval ∘ σ⇒) ∘ (id ⊗₁ [ h , id ]₁)                    ≈⟨ assoc ⟩
  eval ∘ σ⇒ ∘ (id ⊗₁ [ h , id ]₁)                      ≈⟨ refl⟩∘⟨ σ⇒-comm ⟩
  eval ∘ ([ h , id ]₁ ⊗₁ id) ∘ σ⇒                      ≈⟨ pullˡ eval-comm-dom ⟩
  (eval ∘ (id ⊗₁ h)) ∘ σ⇒                              ≈⟨ assoc ⟩
  eval ∘ (id ⊗₁ h) ∘ σ⇒                                ≈˘⟨ refl⟩∘⟨ σ⇒-comm ⟩
  eval ∘ σ⇒ ∘ (h ⊗₁ id)                                ≈⟨ sym-assoc ⟩
  (eval ∘ σ⇒) ∘ (h ⊗₁ id)                              ≈˘⟨ eval-curry ⟩∘⟨refl ⟩
  (eval ∘ (δ D ⊗₁ id)) ∘ (h ⊗₁ id)                     ≈⟨ assoc ⟩
  eval ∘ (δ D ⊗₁ id) ∘ (h ⊗₁ id)                       ≈⟨ refl⟩∘⟨ merge₁ˡ ⟩
  eval ∘ ((δ D ∘ h) ⊗₁ id)                             ∎)

IsDualizing : Pred Obj _
IsDualizing D = ∀ {A} → IsIso (δ {A} D)
