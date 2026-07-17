{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

-- The internal-hom calculus of a monoidal closed category, in equational form:
-- evaluation, currying and its β/η laws, the name of a map, internal composition
-- and its unit laws, and the isomorphism `X ≅ [ unit , X ]`.
--
-- `Closed` is stated as an adjunction `(-⊗ X) ⊣ [ X ,-]`, so `ev` is its counit
-- and `curry` its `Ladjunct`.  Everything below is derived once, here, so that no
-- consumer has to unfold the adjunction again.

module Categories.Category.Monoidal.Closed.Properties
  {o ℓ e} {C : Category o ℓ e} {M : Monoidal C} (Cl : Closed M) where

open import Data.Product using (_,_)

open Closed Cl using ([-,-]; [_,_]₀; [_,_]₁; [_,-]; module adjoint; module mate)

open Category C
open Monoidal M
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Utilities M
open import Categories.Category.Monoidal.Reassociation M
open import Categories.Morphism.Reasoning C
open import Categories.Morphism C using (_≅_)
open Shorthands

open adjoint using (counit; Ladjunct-resp-≈; RLadjunct≈id; LRadjunct≈id)
  renaming (Ladjunct to curry; Ladjunct-comm′ to curry-∘)

private
  variable
    A B W X Y Z : Obj

------------------------------------------------------------------------
-- Evaluation, currying, uncurrying.

-- The counit of `(-⊗ X) ⊣ [ X ,-]`: feed the argument to the function.
ev : [ X , Y ]₀ ⊗₀ X ⇒ Y
ev {X} {Y} = counit.η {X} Y

-- `uncurry g = ev ∘ (g ⊗₁ id)` is `Radjunct` — definitionally, so the adjunction's
-- two triangle laws are exactly β and η for currying.
uncurry : A ⇒ [ X , B ]₀ → A ⊗₀ X ⇒ B
uncurry g = ev ∘ (g ⊗₁ id)

-- β: currying then evaluating gives the map back.
ev-curry : {f : A ⊗₀ X ⇒ B} → uncurry (curry f) ≈ f
ev-curry = RLadjunct≈id

-- η: a map into a hom object is the currying of its uncurrying.
curry-ev : {g : A ⇒ [ X , B ]₀} → curry (uncurry g) ≈ g
curry-ev = LRadjunct≈id

curry-resp-≈ : {f g : A ⊗₀ X ⇒ B} → f ≈ g → curry f ≈ curry g
curry-resp-≈ = Ladjunct-resp-≈

-- Currying is *uniquely* determined by β: nothing else evaluates to `f`.
curry-unique : {f : A ⊗₀ X ⇒ B} {g : A ⇒ [ X , B ]₀} → uncurry g ≈ f → g ≈ curry f
curry-unique {g = g} unc≈f = begin
  g                  ≈˘⟨ curry-ev ⟩
  curry (uncurry g)  ≈⟨ curry-resp-≈ unc≈f ⟩
  curry _            ∎

-- Hence two maps into a hom object agree as soon as their uncurryings do.
uncurry-injective : {g h : A ⇒ [ X , B ]₀} → uncurry g ≈ uncurry h → g ≈ h
uncurry-injective {h = h} g≈h = begin
  _                  ≈⟨ curry-unique g≈h ⟩
  curry (uncurry h)  ≈⟨ curry-ev ⟩
  h                  ∎

------------------------------------------------------------------------
-- Names.  A map `X ⇒ Y` is an element `unit ⇒ [ X , Y ]₀` of the hom object,
-- and evaluating that element is applying the map.

name : X ⇒ Y → unit ⇒ [ X , Y ]₀
name f = curry (f ∘ λ⇒)

ev-name : {f : X ⇒ Y} → uncurry (name f) ≈ f ∘ λ⇒
ev-name = ev-curry

-- The internal identity.
j : unit ⇒ [ X , X ]₀
j = name id

ev-j : uncurry (j {X}) ≈ λ⇒
ev-j = begin
  uncurry (name id)  ≈⟨ ev-name ⟩
  id ∘ λ⇒            ≈⟨ identityˡ ⟩
  λ⇒                 ∎

------------------------------------------------------------------------
-- Internal composition.  `comp` is the currying of "evaluate the right-hand
-- function, then the left-hand one".

comp : [ Y , Z ]₀ ⊗₀ [ X , Y ]₀ ⇒ [ X , Z ]₀
comp = curry (ev ∘ (id ⊗₁ ev) ∘ α⇒)

ev-comp : uncurry (comp {Y} {Z} {X}) ≈ ev ∘ (id ⊗₁ ev) ∘ α⇒
ev-comp = ev-curry

-- Composing with an internal identity does nothing.  Both unit laws are proved by
-- uncurrying: the whiskered `j` meets `ev` and unfolds to a unitor.

comp-idˡ : comp {X = X} ∘ (j {Y} ⊗₁ id) ≈ λ⇒
comp-idˡ {X = X} {Y = Y} = uncurry-injective (begin
  ev ∘ ((comp ∘ (j ⊗₁ id)) ⊗₁ id)          ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
  ev ∘ (comp ⊗₁ id) ∘ ((j ⊗₁ id) ⊗₁ id)    ≈⟨ pullˡ ev-comp ⟩
  (ev ∘ (id ⊗₁ ev) ∘ α⇒) ∘ ((j ⊗₁ id) ⊗₁ id)
    ≈⟨ assoc²βε ⟩
  ev ∘ (id ⊗₁ ev) ∘ α⇒ ∘ ((j ⊗₁ id) ⊗₁ id)  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ α⇒-⊗id-commute ⟩
  ev ∘ (id ⊗₁ ev) ∘ (j ⊗₁ id) ∘ α⇒          ≈⟨ refl⟩∘⟨ extendʳ (⟺ whisker-comm) ⟩
  ev ∘ (j ⊗₁ id) ∘ (id ⊗₁ ev) ∘ α⇒          ≈⟨ pullˡ ev-j ⟩
  λ⇒ ∘ (id ⊗₁ ev) ∘ α⇒                      ≈⟨ pullˡ unitorˡ-commute-from ⟩
  (ev ∘ λ⇒) ∘ α⇒                            ≈⟨ pullʳ coherence₁ ⟩
  ev ∘ (λ⇒ ⊗₁ id)                           ∎)

comp-idʳ : comp {Y = X} {Z = Z} ∘ (id ⊗₁ j {X}) ≈ ρ⇒
comp-idʳ {X = X} {Z = Z} = uncurry-injective (begin
  ev ∘ ((comp ∘ (id ⊗₁ j)) ⊗₁ id)          ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
  ev ∘ (comp ⊗₁ id) ∘ ((id ⊗₁ j) ⊗₁ id)    ≈⟨ pullˡ ev-comp ⟩
  (ev ∘ (id ⊗₁ ev) ∘ α⇒) ∘ ((id ⊗₁ j) ⊗₁ id)
    ≈⟨ assoc²βε ⟩
  ev ∘ (id ⊗₁ ev) ∘ α⇒ ∘ ((id ⊗₁ j) ⊗₁ id)  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-commute-from ⟩
  ev ∘ (id ⊗₁ ev) ∘ (id ⊗₁ (j ⊗₁ id)) ∘ α⇒  ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
  ev ∘ (id ⊗₁ (ev ∘ (j ⊗₁ id))) ∘ α⇒        ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ ev-j) ⟩∘⟨refl ⟩
  ev ∘ (id ⊗₁ λ⇒) ∘ α⇒                      ≈⟨ refl⟩∘⟨ triangle ⟩
  ev ∘ (ρ⇒ ⊗₁ id)                           ∎)

------------------------------------------------------------------------
-- `X ≅ [ unit , X ]₀`.  A function of no arguments is a value.

i⇒ : X ⇒ [ unit , X ]₀
i⇒ = curry ρ⇒

i⇐ : [ unit , X ]₀ ⇒ X
i⇐ = ev ∘ ρ⇐

ev-i⇒ : uncurry (i⇒ {X}) ≈ ρ⇒
ev-i⇒ = ev-curry

i-isoˡ : i⇐ ∘ i⇒ ≈ id {X}
i-isoˡ = begin
  (ev ∘ ρ⇐) ∘ i⇒        ≈⟨ pullʳ unitorʳ-commute-to ⟩
  ev ∘ (i⇒ ⊗₁ id) ∘ ρ⇐  ≈⟨ pullˡ ev-i⇒ ⟩
  ρ⇒ ∘ ρ⇐               ≈⟨ unitorʳ.isoʳ ⟩
  id                    ∎

i-isoʳ : i⇒ ∘ i⇐ ≈ id {[ unit , X ]₀}
i-isoʳ = uncurry-injective (begin
  ev ∘ ((i⇒ ∘ i⇐) ⊗₁ id)          ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
  ev ∘ (i⇒ ⊗₁ id) ∘ (i⇐ ⊗₁ id)    ≈⟨ pullˡ ev-i⇒ ⟩
  ρ⇒ ∘ (i⇐ ⊗₁ id)                 ≈⟨ unitorʳ-commute-from ⟩
  i⇐ ∘ ρ⇒                         ≈⟨ assoc ⟩
  ev ∘ ρ⇐ ∘ ρ⇒                    ≈⟨ refl⟩∘⟨ unitorʳ.isoˡ ⟩
  ev ∘ id                         ≈⟨ identityʳ ⟩
  ev                              ≈˘⟨ elimʳ ⊗.identity ⟩
  ev ∘ (id ⊗₁ id)                 ∎)

i : X ≅ [ unit , X ]₀
i = record { from = i⇒ ; to = i⇐ ; iso = record { isoˡ = i-isoˡ ; isoʳ = i-isoʳ } }

------------------------------------------------------------------------
-- The unit's own hom object, `[ unit , unit ]₀`, is the unit: `j` and `i⇐` are
-- mutually inverse there.  (`i-isoʳ` already gives one half.)

j≈i⇒ : j {unit} ≈ i⇒
j≈i⇒ = uncurry-injective (begin
  uncurry (j {unit})  ≈⟨ ev-j ⟩
  λ⇒                  ≈⟨ coherence₃ ⟩
  ρ⇒                  ≈˘⟨ ev-i⇒ ⟩
  uncurry i⇒          ∎)

i⇐-j : i⇐ ∘ j {unit} ≈ id
i⇐-j = begin
  i⇐ ∘ j    ≈⟨ refl⟩∘⟨ j≈i⇒ ⟩
  i⇐ ∘ i⇒   ≈⟨ i-isoˡ ⟩
  id        ∎

------------------------------------------------------------------------
-- Evaluation is composition with a value.  Read the argument as a map out of the
-- unit (`i⇒`), compose internally, and read the result back (`i⇐`): that is `ev`.
-- This is what lets an argument be traded for a function of no arguments.

private
  -- A right unitor swallows the associator in front of it.
  ρ⇒-α⇒ : (id {X} ⊗₁ ρ⇒ {Y}) ∘ α⇒ ≈ ρ⇒
  ρ⇒-α⇒ = begin
    (id ⊗₁ ρ⇒) ∘ α⇒  ≈˘⟨ ρ⇒-assoc ⟩∘⟨refl ⟩
    (ρ⇒ ∘ α⇐) ∘ α⇒   ≈⟨ cancelʳ associator.isoˡ ⟩
    ρ⇒               ∎

comp-i : i⇐ ∘ comp {Y} {Z} {unit} ∘ (id ⊗₁ i⇒) ≈ ev
comp-i = begin
  (ev ∘ ρ⇐) ∘ comp ∘ (id ⊗₁ i⇒)                    ≈⟨ assoc ⟩
  ev ∘ ρ⇐ ∘ comp ∘ (id ⊗₁ i⇒)                      ≈⟨ refl⟩∘⟨ pullˡ unitorʳ-commute-to ⟩
  ev ∘ ((comp ⊗₁ id) ∘ ρ⇐) ∘ (id ⊗₁ i⇒)            ≈⟨ refl⟩∘⟨ assoc ⟩
  ev ∘ (comp ⊗₁ id) ∘ ρ⇐ ∘ (id ⊗₁ i⇒)              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ unitorʳ-commute-to ⟩
  ev ∘ (comp ⊗₁ id) ∘ ((id ⊗₁ i⇒) ⊗₁ id) ∘ ρ⇐      ≈⟨ pullˡ ev-comp ⟩
  (ev ∘ (id ⊗₁ ev) ∘ α⇒) ∘ ((id ⊗₁ i⇒) ⊗₁ id) ∘ ρ⇐  ≈⟨ assoc²βε ⟩
  ev ∘ (id ⊗₁ ev) ∘ α⇒ ∘ ((id ⊗₁ i⇒) ⊗₁ id) ∘ ρ⇐
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟩
  ev ∘ (id ⊗₁ ev) ∘ (id ⊗₁ (i⇒ ⊗₁ id)) ∘ α⇒ ∘ ρ⇐   ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
  ev ∘ (id ⊗₁ (ev ∘ (i⇒ ⊗₁ id))) ∘ α⇒ ∘ ρ⇐         ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ ev-i⇒) ⟩∘⟨refl ⟩
  ev ∘ (id ⊗₁ ρ⇒) ∘ α⇒ ∘ ρ⇐                        ≈⟨ refl⟩∘⟨ pullˡ ρ⇒-α⇒ ⟩
  ev ∘ ρ⇒ ∘ ρ⇐                                     ≈⟨ elimʳ unitorʳ.isoʳ ⟩
  ev                                               ∎
