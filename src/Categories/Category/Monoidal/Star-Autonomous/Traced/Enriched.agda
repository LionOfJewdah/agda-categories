{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Monoidal.Traced using (Traced)

-- Enriched (ℂ-)naturality tools for the traced ∗-autonomous development.  The
-- extranaturality hexagon of `Closed/CompactClosed.agda` is the *enriched*
-- extraordinary naturality of the unit `t` (Hajgató & Hasegawa, TAC 28(7), 2013,
-- Lemma 3.3 / Corollary 3.4).  To reach it we need the internal (enriched) action
-- of the closed-structure functors out of which `φ` is built — first of all the
-- internal action of dualization `[ - , ⊥ ]`.

module Categories.Category.Monoidal.Star-Autonomous.Traced.Enriched
  {o ℓ e} {𝒞 : Category o ℓ e} {M : Monoidal 𝒞}
  (Cl : Closed M) (T : Traced M) where

open import Data.Product using (_,_)

open import Categories.Category.Monoidal.Symmetric M using (Symmetric)

open Category 𝒞
open Monoidal M
open Traced T using (symmetric)
open Symmetric symmetric using (braiding; commutative)
open Closed Cl using ([_,_]₀; [_,_]₁; [-,_]; [_,-]; [-,-])

open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Reassociation M
open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Utilities M
open import Categories.Category.Monoidal.Braided.Properties (Symmetric.braided symmetric)
  renaming (module Shorthands to BraidShorthands)
open import Categories.Category.Monoidal.Closed.Properties Cl
open import Categories.Morphism 𝒞 using (_≅_; module ≅)
open import Categories.Morphism.Reasoning 𝒞
open Shorthands
open BraidShorthands

open import Categories.Category.Monoidal.Star-Autonomous.Traced.Duality Cl T public

private
  variable
    A B C D X Y Z : Obj

------------------------------------------------------------------------
-- The internal action of dualization `[ - , ⊥ ]` at the fixed codomain `⊥`.
-- `dual-int : [ A , B ]₀ ⇒ [ B * , A * ]₀` sends a function to "precompose with
-- it": internally, `g : B *` becomes `g ∘ f : A *`.  It is `internal-∘` after the
-- braiding, curried.

module _ (⊥ : Obj) (dualizing : IsDualizing ⊥) where
  open Dualized ⊥ dualizing

  dual-int : [ A , B ]₀ ⇒ [ B * , A * ]₀
  dual-int = curry (internal-∘ ∘ σ⇒)
