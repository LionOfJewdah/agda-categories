{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Monoidal.Traced using (Traced)

-- Traced ∗-autonomous categories are compact closed (Hajgató & Hasegawa, TAC
-- 28(7), 2013).  A traced ∗-autonomous category is a symmetric monoidal closed
-- category with a trace on its symmetric monoidal structure and a dualizing
-- object `⊥`.  Its unit map `t : unit ⇒ X ⊗₀ X *` is produced from the trace of
-- evaluation, and — after correcting by `t {unit} ⁻¹` — satisfies the two snake
-- equations, so the category is compact closed (`Closed/CompactClosed.agda`).
--
-- This file is the paper's §3: it *produces* the extranatural `t` that
-- `Closed/CompactClosed.agda` (their Prop 2.1) turns into compact closure.

module Categories.Category.Monoidal.Star-Autonomous.Traced
  {o ℓ e} {𝒞 : Category o ℓ e} {M : Monoidal 𝒞}
  (Cl : Closed M) (T : Traced M) where

open import Data.Product using (_,_)
open import Relation.Unary using (Pred)

open import Categories.Category.Monoidal.Symmetric M using (Symmetric)

open Category 𝒞
open Monoidal M
open Traced T using (trace; trace⟨_⟩; slide; tightenₗ; tightenᵣ; vanishing₁; superposing; symmetric)
open Symmetric symmetric using (braiding; commutative)
open Closed Cl using ([_,_]₀; [_,_]₁; [-,_]; [_,-]; [-,-])

open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Reassociation M using (whisker-comm)
open import Categories.Category.Monoidal.Utilities M using (module Shorthands)
open import Categories.Category.Monoidal.Braided.Properties (Symmetric.braided symmetric)
  renaming (module Shorthands to BraidShorthands)
open import Categories.Category.Monoidal.Closed.Properties Cl
open import Categories.Morphism 𝒞 using (_≅_; Iso; IsIso; module ≅)
open import Categories.Morphism.Duality 𝒞 using (≅⇒op-≅)
open import Categories.Morphism.Reasoning 𝒞
open import Categories.Functor.Properties using ([_]-resp-≅)
open Shorthands
open BraidShorthands using (σ⇒; σ⇒-comm)

private
  variable
    A B C X Y Z : Obj

------------------------------------------------------------------------
-- `τ` — the trace of evaluation.  `τ^X_B : [ X , B ⊗₀ X ]₀ ⇒ B` is the trace,
-- over `X`, of `ev : [ X , B ⊗₀ X ]₀ ⊗₀ X ⇒ B ⊗₀ X`.  Tracing out `X` leaves a
-- map that reads a function and returns the `B` component of its self-application.

τ : [ X , B ⊗₀ X ]₀ ⇒ B
τ {X} {B} = trace {X = X} (eval {X} {B ⊗₀ X})

-- Its name, the ∗-autonomous transpose of the paper: `unit ⇒ [ [ X , B ⊗₀ X ]₀ , B ]₀`.
τ̂ : unit ⇒ [ [ X , B ⊗₀ X ]₀ , B ]₀
τ̂ = ⌜ τ ⌝

-- `τ` determines the whole trace (paper, p. 207): the trace of any `f : A ⊗₀ X ⇒ B ⊗₀ X`
-- is `τ` applied to the name of `f`.  Tightening pulls `curry f` out of the trace, where it
-- meets `ev` and β-reduces.
trace-from-τ : {f : A ⊗₀ X ⇒ B ⊗₀ X} → τ {X} {B} ∘ curry f ≈ trace f
trace-from-τ {f = f} = begin
  τ ∘ curry f                     ≈˘⟨ tightenᵣ ⟩
  trace (eval ∘ (curry f ⊗₁ id))  ≈⟨ trace⟨ eval-curry ⟩ ⟩
  trace f                         ∎

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

-- The dualizing hypothesis, packaged as the double-dual isomorphism.
module Dualized (⊥ : Obj) (dualizing : IsDualizing ⊥) where

  infix 30 _*
  _* : Obj → Obj
  A * = [ A , ⊥ ]₀

  -- `A` is its own double dual.
  **-≅ : A ≅ (A *) *
  **-≅ {A} = record
    { from = δ ⊥
    ; to   = IsIso.inv dualizing
    ; iso  = IsIso.iso dualizing
    }

  -- `⊥ *` is the unit.  `[ unit , ⊥ ]₀ ≅ ⊥` (a value is a nullary function), lifted
  -- through `[ - , ⊥ ]`, turns `unit`'s double dual into `⊥ *`.
  ⊥*-≅ : (⊥ *) ≅ unit
  ⊥*-≅ = ≅.trans ([ [-, ⊥ ] ]-resp-≅ (≅⇒op-≅ (unit-hom {⊥}))) (≅.sym (**-≅ {unit}))

  -- Lift an isomorphism through dualization `[ - , ⊥ ]`.
  dualᵒ : {A B : Obj} → A ≅ B → (A *) ≅ (B *)
  dualᵒ iso = [ [-, ⊥ ] ]-resp-≅ (≅⇒op-≅ iso)

  ----------------------------------------------------------------------
  -- Lemma 3.2.  The ∗-autonomous isomorphism `φ`, as the five-step chain of p. 210:
  -- the double dual on `⊥ ⊗₀ Y`, swap-currying `[ ⊥ ⊗₀ Y , ⊥ ]₀ ≅ [ Y , [ ⊥ , ⊥ ]₀ ]₀`,
  -- `[ ⊥ , ⊥ ]₀ ≅ unit`, currying back `[ X , [ [ Y , unit ]₀ , ⊥ ]₀ ]₀ ≅ (X ⊗₀ [ Y , unit ]₀) *`,
  -- and the double dual on `X ⊗₀ [ Y , unit ]₀`.  Each inner step is lifted through the
  -- surrounding hom functors by `homˡ`/`dualᵒ`.
  φ-≅ : ([ X , ⊥ ⊗₀ Y ]₀ *) ≅ X ⊗₀ [ Y , unit ]₀
  φ-≅ {X} {Y} =
    ≅.trans (dualᵒ (homˡ X (**-≅ {⊥ ⊗₀ Y})))
   (≅.trans (dualᵒ (homˡ X (dualᵒ (swap-curry-≅ {⊥} {Y} {⊥}))))
   (≅.trans (dualᵒ (homˡ X (dualᵒ (homˡ Y ⊥*-≅))))
   (≅.trans (dualᵒ (≅.sym (curry₂-iso {X} {[ Y , unit ]₀} {⊥})))
            (≅.sym (**-≅ {X ⊗₀ [ Y , unit ]₀})))))
