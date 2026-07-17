{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

-- The internal-hom calculus of a monoidal closed category, in equational form:
-- evaluation, currying and its β/η laws, the name `⌜_⌝` of a map, internal composition
-- and its unit laws, and the isomorphism `X ≅ [ unit , X ]`.
--
-- `Closed` is stated as an adjunction `(-⊗ X) ⊣ [ X ,-]`, so `eval` is its counit
-- and `curry` its `Ladjunct`.  Everything below is derived once, here, so that no
-- consumer has to unfold the adjunction again.

module Categories.Category.Monoidal.Closed.Properties
  {o ℓ e} {𝒞 : Category o ℓ e} {M : Monoidal 𝒞} (Cl : Closed M) where

open import Data.Product using (_,_)

open Closed Cl using ([-,-]; [_,_]₀; [_,_]₁; [_,-]; module adjoint; module mate)

open Category 𝒞
open Monoidal M
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Utilities M
open import Categories.Category.Monoidal.Reassociation M
open import Categories.Morphism.Reasoning 𝒞
open import Categories.Morphism 𝒞 using (_≅_)
open import Categories.Functor.Bifunctor.Properties using ([_]-decompose₂)
open Shorthands

open import Categories.Category.Product using (Product; _※_; _⁂_; πˡ; πʳ)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

open adjoint using (counit)
open adjoint public using ()
  renaming (
    Ladjunct to curry; Ladjunct-comm′ to curry-∘
    ; RLadjunct≈id to eval-curry -- β: currying then evaluating gives the map back
    ; LRadjunct≈id to curry-eval -- η: a map into a hom object is the currying of its uncurrying
    ; Ladjunct-resp-≈ to curry-resp-≈
  )

private
  variable
    A B C W X Y Z : Obj

------------------------------------------------------------------------
-- Evaluation, currying, uncurrying.

-- The counit of `(-⊗ X) ⊣ [ X ,-]`: feed the argument to the function.
eval : [ X , Y ]₀ ⊗₀ X ⇒ Y
eval {X} {Y} = counit.η {X} Y

-- `uncurry g = eval ∘ (g ⊗₁ id)` is `Radjunct` — definitionally, so the adjunction's
-- two triangle laws are exactly β and η for currying.
uncurry : A ⇒ [ X , B ]₀ → A ⊗₀ X ⇒ B
uncurry g = eval ∘ (g ⊗₁ id)

-- Currying is *uniquely* determined by β: nothing else evaluates to `f`.
curry-unique : {f : A ⊗₀ X ⇒ B} {g : A ⇒ [ X , B ]₀} → uncurry g ≈ f → g ≈ curry f
curry-unique {g = g} unc≈f = begin
  g                  ≈˘⟨ curry-eval ⟩
  curry (uncurry g)  ≈⟨ curry-resp-≈ unc≈f ⟩
  curry _            ∎

-- Hence two maps into a hom object agree as soon as their uncurryings do.
uncurry-injective : {g h : A ⇒ [ X , B ]₀} → uncurry g ≈ uncurry h → g ≈ h
uncurry-injective {h = h} g≈h = begin
  _                  ≈⟨ curry-unique g≈h ⟩
  curry (uncurry h)  ≈⟨ curry-eval ⟩
  h                  ∎

-- Evaluation is natural in the codomain (the covariant hom slot): apply, then
-- post-compose `g`, equals post-composing `g` inside the function first.  This is
-- exactly the naturality of the adjunction counit.
eval-comm-cod : {g : X ⇒ Y} → eval {A} {Y} ∘ ([ id , g ]₁ ⊗₁ id) ≈ g ∘ eval
eval-comm-cod {g = g} = counit.commute g

-- Evaluation is natural in the domain (the contravariant hom slot): reindexing a
-- function's argument along `f` and then applying agrees with applying `f` to the
-- argument first.  This is the mate law relating the `(-⊗ A)` and `(-⊗ B)` adjunctions.
eval-comm-dom : {f : A ⇒ B} → eval {A} {Y} ∘ ([ f , id ]₁ ⊗₁ id) ≈ eval {B} {Y} ∘ (id ⊗₁ f)
eval-comm-dom {f = f} = mate.commute₂ f

-- The full naturality of evaluation, combining both slots: `[ p , q ]₁` reindexes the
-- argument by `p` and post-composes `q`.
eval-comm : {p : A ⇒ B} {q : X ⇒ Y} → eval {A} {Y} ∘ ([ p , q ]₁ ⊗₁ id) ≈ q ∘ eval ∘ (id ⊗₁ p)
eval-comm {p = p} {q = q} = begin
  eval ∘ ([ p , q ]₁ ⊗₁ id)                          ≈⟨ refl⟩∘⟨ ([ [-,-] ]-decompose₂ ⟩⊗⟨refl) ⟩
  eval ∘ (([ id , q ]₁ ∘ [ p , id ]₁) ⊗₁ id)         ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
  eval ∘ ([ id , q ]₁ ⊗₁ id) ∘ ([ p , id ]₁ ⊗₁ id)   ≈⟨ pullˡ eval-comm-cod ⟩
  (q ∘ eval) ∘ ([ p , id ]₁ ⊗₁ id)                   ≈⟨ assoc ⟩
  q ∘ eval ∘ ([ p , id ]₁ ⊗₁ id)                     ≈⟨ refl⟩∘⟨ eval-comm-dom ⟩
  q ∘ eval ∘ (id ⊗₁ p)                               ∎

------------------------------------------------------------------------
-- Names.  A map `X ⇒ Y` is an element `unit ⇒ [ X , Y ]₀` of the hom object,
-- and evaluating that element is applying the map.  `⌜ f ⌝` is the name of `f`.

⌜_⌝ : X ⇒ Y → unit ⇒ [ X , Y ]₀
⌜ f ⌝ = curry (f ∘ λ⇒)

eval-⌜⌝ : {f : X ⇒ Y} → uncurry ⌜ f ⌝ ≈ f ∘ λ⇒
eval-⌜⌝ = eval-curry

-- The internal identity.
⌜id⌝ : unit ⇒ [ X , X ]₀
⌜id⌝ = ⌜ id ⌝

eval-⌜id⌝ : uncurry (⌜id⌝ {X}) ≈ λ⇒
eval-⌜id⌝ = begin
  uncurry ⌜ id ⌝  ≈⟨ eval-⌜⌝ ⟩
  id ∘ λ⇒         ≈⟨ identityˡ ⟩
  λ⇒              ∎

------------------------------------------------------------------------
-- Internal composition: the currying of "evaluate the right-hand function, then
-- the left-hand one".

internal-∘ : [ Y , Z ]₀ ⊗₀ [ X , Y ]₀ ⇒ [ X , Z ]₀
internal-∘ = curry (eval ∘ (id ⊗₁ eval) ∘ α⇒)

eval-internal-∘ : uncurry (internal-∘ {Y} {Z} {X}) ≈ eval ∘ (id ⊗₁ eval) ∘ α⇒
eval-internal-∘ = eval-curry

-- Composing with an internal identity does nothing.  Both unit laws are proved by
-- uncurrying: the whiskered `j` meets `ev` and unfolds to a unitor.

internal-∘-idˡ : internal-∘ {X = X} ∘ (⌜id⌝ {Y} ⊗₁ id) ≈ λ⇒
internal-∘-idˡ {X = X} {Y = Y} = uncurry-injective (begin
  eval ∘ ((internal-∘ ∘ (⌜id⌝ ⊗₁ id)) ⊗₁ id)          ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
  eval ∘ (internal-∘ ⊗₁ id) ∘ ((⌜id⌝ ⊗₁ id) ⊗₁ id)    ≈⟨ pullˡ eval-internal-∘ ⟩
  (eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ ((⌜id⌝ ⊗₁ id) ⊗₁ id)
    ≈⟨ assoc²βε ⟩
  eval ∘ (id ⊗₁ eval) ∘ α⇒ ∘ ((⌜id⌝ ⊗₁ id) ⊗₁ id)  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ α⇒-⊗id-commute ⟩
  eval ∘ (id ⊗₁ eval) ∘ (⌜id⌝ ⊗₁ id) ∘ α⇒          ≈⟨ refl⟩∘⟨ extendʳ (⟺ whisker-comm) ⟩
  eval ∘ (⌜id⌝ ⊗₁ id) ∘ (id ⊗₁ eval) ∘ α⇒          ≈⟨ pullˡ eval-⌜id⌝ ⟩
  λ⇒ ∘ (id ⊗₁ eval) ∘ α⇒                      ≈⟨ pullˡ unitorˡ-commute-from ⟩
  (eval ∘ λ⇒) ∘ α⇒                            ≈⟨ pullʳ coherence₁ ⟩
  eval ∘ (λ⇒ ⊗₁ id)                           ∎)

internal-∘-idʳ : internal-∘ {Y = X} {Z = Z} ∘ (id ⊗₁ ⌜id⌝ {X}) ≈ ρ⇒
internal-∘-idʳ {X = X} {Z = Z} = uncurry-injective (begin
  eval ∘ ((internal-∘ ∘ (id ⊗₁ ⌜id⌝)) ⊗₁ id)          ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
  eval ∘ (internal-∘ ⊗₁ id) ∘ ((id ⊗₁ ⌜id⌝) ⊗₁ id)    ≈⟨ pullˡ eval-internal-∘ ⟩
  (eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ ((id ⊗₁ ⌜id⌝) ⊗₁ id)
    ≈⟨ assoc²βε ⟩
  eval ∘ (id ⊗₁ eval) ∘ α⇒ ∘ ((id ⊗₁ ⌜id⌝) ⊗₁ id)  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-commute-from ⟩
  eval ∘ (id ⊗₁ eval) ∘ (id ⊗₁ (⌜id⌝ ⊗₁ id)) ∘ α⇒  ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
  eval ∘ (id ⊗₁ (eval ∘ (⌜id⌝ ⊗₁ id))) ∘ α⇒        ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ eval-⌜id⌝) ⟩∘⟨refl ⟩
  eval ∘ (id ⊗₁ λ⇒) ∘ α⇒                      ≈⟨ refl⟩∘⟨ triangle ⟩
  eval ∘ (ρ⇒ ⊗₁ id)                           ∎)

------------------------------------------------------------------------
-- `unit-hom : X ≅ [ unit , X ]₀`.  A function of no arguments is a value.

unit-hom⇒ : X ⇒ [ unit , X ]₀
unit-hom⇒ = curry ρ⇒

unit-hom⇐ : [ unit , X ]₀ ⇒ X
unit-hom⇐ = eval ∘ ρ⇐

eval-unit-hom⇒ : uncurry (unit-hom⇒ {X}) ≈ ρ⇒
eval-unit-hom⇒ = eval-curry

unit-hom-isoˡ : unit-hom⇐ ∘ unit-hom⇒ ≈ id {X}
unit-hom-isoˡ = begin
  (eval ∘ ρ⇐) ∘ unit-hom⇒        ≈⟨ pullʳ unitorʳ-commute-to ⟩
  eval ∘ (unit-hom⇒ ⊗₁ id) ∘ ρ⇐  ≈⟨ pullˡ eval-unit-hom⇒ ⟩
  ρ⇒ ∘ ρ⇐               ≈⟨ unitorʳ.isoʳ ⟩
  id                    ∎

unit-hom-isoʳ : unit-hom⇒ ∘ unit-hom⇐ ≈ id {[ unit , X ]₀}
unit-hom-isoʳ = uncurry-injective (begin
  eval ∘ ((unit-hom⇒ ∘ unit-hom⇐) ⊗₁ id)          ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
  eval ∘ (unit-hom⇒ ⊗₁ id) ∘ (unit-hom⇐ ⊗₁ id)    ≈⟨ pullˡ eval-unit-hom⇒ ⟩
  ρ⇒ ∘ (unit-hom⇐ ⊗₁ id)                 ≈⟨ unitorʳ-commute-from ⟩
  unit-hom⇐ ∘ ρ⇒                         ≈⟨ assoc ⟩
  eval ∘ ρ⇐ ∘ ρ⇒                    ≈⟨ refl⟩∘⟨ unitorʳ.isoˡ ⟩
  eval ∘ id                         ≈⟨ identityʳ ⟩
  eval                              ≈˘⟨ elimʳ ⊗.identity ⟩
  eval ∘ (id ⊗₁ id)                 ∎)

unit-hom : X ≅ [ unit , X ]₀
unit-hom = record { from = unit-hom⇒ ; to = unit-hom⇐ ; iso = record { isoˡ = unit-hom-isoˡ ; isoʳ = unit-hom-isoʳ } }

------------------------------------------------------------------------
-- The unit's own hom object, `[ unit , unit ]₀`, is the unit: `j` and `i⇐` are
-- mutually inverse there.  (`i-isoʳ` already gives one half.)

⌜id⌝≈unit-hom⇒ : ⌜id⌝ {unit} ≈ unit-hom⇒
⌜id⌝≈unit-hom⇒ = uncurry-injective (begin
  uncurry (⌜id⌝ {unit})  ≈⟨ eval-⌜id⌝ ⟩
  λ⇒                  ≈⟨ coherence₃ ⟩
  ρ⇒                  ≈˘⟨ eval-unit-hom⇒ ⟩
  uncurry unit-hom⇒          ∎)

unit-hom⇐-⌜id⌝ : unit-hom⇐ ∘ ⌜id⌝ {unit} ≈ id
unit-hom⇐-⌜id⌝ = begin
  unit-hom⇐ ∘ ⌜id⌝    ≈⟨ refl⟩∘⟨ ⌜id⌝≈unit-hom⇒ ⟩
  unit-hom⇐ ∘ unit-hom⇒   ≈⟨ unit-hom-isoˡ ⟩
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

internal-∘-unit-hom : unit-hom⇐ ∘ internal-∘ {Y} {Z} {unit} ∘ (id ⊗₁ unit-hom⇒) ≈ eval
internal-∘-unit-hom = begin
  (eval ∘ ρ⇐) ∘ internal-∘ ∘ (id ⊗₁ unit-hom⇒)                    ≈⟨ assoc ⟩
  eval ∘ ρ⇐ ∘ internal-∘ ∘ (id ⊗₁ unit-hom⇒)                      ≈⟨ refl⟩∘⟨ pullˡ unitorʳ-commute-to ⟩
  eval ∘ ((internal-∘ ⊗₁ id) ∘ ρ⇐) ∘ (id ⊗₁ unit-hom⇒)            ≈⟨ refl⟩∘⟨ assoc ⟩
  eval ∘ (internal-∘ ⊗₁ id) ∘ ρ⇐ ∘ (id ⊗₁ unit-hom⇒)              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ unitorʳ-commute-to ⟩
  eval ∘ (internal-∘ ⊗₁ id) ∘ ((id ⊗₁ unit-hom⇒) ⊗₁ id) ∘ ρ⇐      ≈⟨ pullˡ eval-internal-∘ ⟩
  (eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ ((id ⊗₁ unit-hom⇒) ⊗₁ id) ∘ ρ⇐  ≈⟨ assoc²βε ⟩
  eval ∘ (id ⊗₁ eval) ∘ α⇒ ∘ ((id ⊗₁ unit-hom⇒) ⊗₁ id) ∘ ρ⇐
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟩
  eval ∘ (id ⊗₁ eval) ∘ (id ⊗₁ (unit-hom⇒ ⊗₁ id)) ∘ α⇒ ∘ ρ⇐   ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
  eval ∘ (id ⊗₁ (eval ∘ (unit-hom⇒ ⊗₁ id))) ∘ α⇒ ∘ ρ⇐         ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ eval-unit-hom⇒) ⟩∘⟨refl ⟩
  eval ∘ (id ⊗₁ ρ⇒) ∘ α⇒ ∘ ρ⇐                        ≈⟨ refl⟩∘⟨ pullˡ ρ⇒-α⇒ ⟩
  eval ∘ ρ⇒ ∘ ρ⇐                                     ≈⟨ elimʳ unitorʳ.isoʳ ⟩
  eval                                               ∎

------------------------------------------------------------------------
-- The currying isomorphism `[ A ⊗₀ B , C ]₀ ≅ [ A , [ B , C ]₀ ]₀`.  A function of a
-- pair is a function of the first argument returning a function of the second; the two
-- associators inside `curry₂`/`uncurry₂` re-bracket `(W ⊗₀ A) ⊗₀ B` and `W ⊗₀ (A ⊗₀ B)`.

-- Uncurrying distributes over precomposition (whiskered into the argument), and
-- respects equality of the argument.
uncurry-∘ : {g : B ⇒ [ X , Y ]₀} {h : A ⇒ B} → uncurry (g ∘ h) ≈ uncurry g ∘ (h ⊗₁ id)
uncurry-∘ = (refl⟩∘⟨ split₁ˡ) ○ sym-assoc

uncurry-resp-≈ : {g h : A ⇒ [ X , Y ]₀} → g ≈ h → uncurry g ≈ uncurry h
uncurry-resp-≈ p = refl⟩∘⟨ (p ⟩⊗⟨refl)

curry₂ : [ A ⊗₀ B , C ]₀ ⇒ [ A , [ B , C ]₀ ]₀
curry₂ = curry (curry (eval ∘ α⇒))

uncurry₂ : [ A , [ B , C ]₀ ]₀ ⇒ [ A ⊗₀ B , C ]₀
uncurry₂ = curry (uncurry eval ∘ α⇐)

curry₂-iso-uncurry₂ : uncurry₂ {A} {B} {C} ∘ curry₂ ≈ id
curry₂-iso-uncurry₂ = uncurry-injective (begin
  uncurry (uncurry₂ ∘ curry₂)                        ≈⟨ uncurry-∘ ⟩
  uncurry uncurry₂ ∘ (curry₂ ⊗₁ id)                  ≈⟨ eval-curry ⟩∘⟨refl ⟩
  (uncurry eval ∘ α⇐) ∘ (curry₂ ⊗₁ id)                 ≈⟨ assoc ⟩
  uncurry eval ∘ α⇐ ∘ (curry₂ ⊗₁ id)                   ≈⟨ refl⟩∘⟨ α⇐-⊗id-commute ⟩
  uncurry eval ∘ ((curry₂ ⊗₁ id) ⊗₁ id) ∘ α⇐           ≈⟨ sym-assoc ⟩
  (uncurry eval ∘ ((curry₂ ⊗₁ id) ⊗₁ id)) ∘ α⇐         ≈˘⟨ uncurry-∘ ⟩∘⟨refl ⟩
  uncurry (eval ∘ (curry₂ ⊗₁ id)) ∘ α⇐                 ≈⟨ uncurry-resp-≈ eval-curry ⟩∘⟨refl ⟩
  uncurry (curry (eval ∘ α⇒)) ∘ α⇐                     ≈⟨ eval-curry ⟩∘⟨refl ⟩
  (eval ∘ α⇒) ∘ α⇐                                     ≈⟨ cancelʳ associator.isoʳ ⟩
  eval                                                 ≈˘⟨ elimʳ ⊗.identity ⟩
  eval ∘ (id ⊗₁ id)                                    ∎)

-- Two maps into a doubly-iterated hom object agree when their double uncurryings do.
uncurry²-injective : {g h : W ⇒ [ A , [ B , C ]₀ ]₀} →
  uncurry (uncurry g) ≈ uncurry (uncurry h) → g ≈ h
uncurry²-injective p = uncurry-injective (uncurry-injective p)

uncurry₂-iso-curry₂ : curry₂ {A} {B} {C} ∘ uncurry₂ ≈ id
uncurry₂-iso-curry₂ = uncurry²-injective (begin
  uncurry (uncurry (curry₂ ∘ uncurry₂))              ≈⟨ uncurry-resp-≈ uncurry-∘ ⟩
  uncurry (uncurry curry₂ ∘ (uncurry₂ ⊗₁ id))        ≈⟨ uncurry-∘ ⟩
  uncurry (uncurry curry₂) ∘ ((uncurry₂ ⊗₁ id) ⊗₁ id)
    ≈⟨ uncurry-resp-≈ eval-curry ⟩∘⟨refl ⟩
  uncurry (curry (eval ∘ α⇒)) ∘ ((uncurry₂ ⊗₁ id) ⊗₁ id)
    ≈⟨ eval-curry ⟩∘⟨refl ⟩
  (eval ∘ α⇒) ∘ ((uncurry₂ ⊗₁ id) ⊗₁ id)              ≈⟨ pullʳ α⇒-⊗id-commute ⟩
  eval ∘ (uncurry₂ ⊗₁ id) ∘ α⇒                        ≈⟨ pullˡ eval-curry ⟩
  (uncurry eval ∘ α⇐) ∘ α⇒                            ≈⟨ cancelʳ associator.isoˡ ⟩
  uncurry eval                                        ≈˘⟨ uncurry-resp-≈ (elimʳ ⊗.identity) ⟩
  uncurry (eval ∘ (id ⊗₁ id))                         ∎)

curry₂-iso : [ A ⊗₀ B , C ]₀ ≅ [ A , [ B , C ]₀ ]₀
curry₂-iso = record
  { from = curry₂ ; to = uncurry₂
  ; iso = record { isoˡ = curry₂-iso-uncurry₂ ; isoʳ = uncurry₂-iso-curry₂ } }

-- Double β for `curry₂`: uncurrying it twice recovers `ev ∘ α⇒`.
uncurry²-curry₂ : uncurry (uncurry (curry₂ {A} {B} {C})) ≈ eval ∘ α⇒
uncurry²-curry₂ = uncurry-resp-≈ eval-curry ○ eval-curry

-- Naturality of the currying isomorphism.  `curry₂` is a natural transformation,
-- contravariant in `A` and `B`, covariant in `C`.  Double-uncurrying both sides and
-- reducing evaluation past the hom-functor actions (`ev-comm`) lands both on the common
-- form `h ∘ eval ∘ (id ⊗₁ (f ⊗₁ g)) ∘ α⇒`.
curry₂-natural : {f : X ⇒ A} {g : Y ⇒ B} {h : C ⇒ Z} →
  [ f , [ g , h ]₁ ]₁ ∘ curry₂ ≈ curry₂ ∘ [ f ⊗₁ g , h ]₁
curry₂-natural {f = f} {g = g} {h = h} = uncurry²-injective (lhs ○ ⟺ rhs)
  where
    reduce-ev : (eval ∘ (id ⊗₁ g)) ∘ (curry (eval ∘ α⇒) ⊗₁ id) ≈ (eval ∘ α⇒) ∘ (id ⊗₁ g)
    reduce-ev = begin
      (eval ∘ (id ⊗₁ g)) ∘ (curry (eval ∘ α⇒) ⊗₁ id)  ≈⟨ assoc ⟩
      eval ∘ (id ⊗₁ g) ∘ (curry (eval ∘ α⇒) ⊗₁ id)    ≈˘⟨ refl⟩∘⟨ serialize₂₁ ⟩
      eval ∘ (curry (eval ∘ α⇒) ⊗₁ g)                  ≈⟨ refl⟩∘⟨ serialize₁₂ ⟩
      eval ∘ (curry (eval ∘ α⇒) ⊗₁ id) ∘ (id ⊗₁ g)    ≈⟨ pullˡ eval-curry ⟩
      (eval ∘ α⇒) ∘ (id ⊗₁ g)                        ∎
    core : (eval ∘ (id ⊗₁ g)) ∘ (curry (eval ∘ α⇒) ⊗₁ id) ∘ ((id ⊗₁ f) ⊗₁ id)
         ≈ eval ∘ (id ⊗₁ (f ⊗₁ g)) ∘ α⇒
    core = begin
      (eval ∘ (id ⊗₁ g)) ∘ (curry (eval ∘ α⇒) ⊗₁ id) ∘ ((id ⊗₁ f) ⊗₁ id)
        ≈⟨ sym-assoc ⟩
      ((eval ∘ (id ⊗₁ g)) ∘ (curry (eval ∘ α⇒) ⊗₁ id)) ∘ ((id ⊗₁ f) ⊗₁ id)
        ≈⟨ reduce-ev ⟩∘⟨refl ⟩
      ((eval ∘ α⇒) ∘ (id ⊗₁ g)) ∘ ((id ⊗₁ f) ⊗₁ id)
        ≈⟨ assoc ⟩
      (eval ∘ α⇒) ∘ ((id ⊗₁ g) ∘ ((id ⊗₁ f) ⊗₁ id))
        ≈⟨ refl⟩∘⟨ merge₂ˡ ⟩
      (eval ∘ α⇒) ∘ ((id ⊗₁ f) ⊗₁ (g ∘ id))
        ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ identityʳ) ⟩
      (eval ∘ α⇒) ∘ ((id ⊗₁ f) ⊗₁ g)
        ≈⟨ assoc ⟩
      eval ∘ α⇒ ∘ ((id ⊗₁ f) ⊗₁ g)
        ≈⟨ refl⟩∘⟨ assoc-commute-from ⟩
      eval ∘ (id ⊗₁ (f ⊗₁ g)) ∘ α⇒
        ∎
    rhs : uncurry (uncurry (curry₂ ∘ [ f ⊗₁ g , h ]₁)) ≈ h ∘ eval ∘ (id ⊗₁ (f ⊗₁ g)) ∘ α⇒
    rhs = begin
      uncurry (uncurry (curry₂ ∘ [ f ⊗₁ g , h ]₁))
        ≈⟨ uncurry-resp-≈ uncurry-∘ ⟩
      uncurry (uncurry curry₂ ∘ ([ f ⊗₁ g , h ]₁ ⊗₁ id))
        ≈⟨ uncurry-∘ ⟩
      uncurry (uncurry curry₂) ∘ (([ f ⊗₁ g , h ]₁ ⊗₁ id) ⊗₁ id)
        ≈⟨ uncurry²-curry₂ ⟩∘⟨refl ⟩
      (eval ∘ α⇒) ∘ (([ f ⊗₁ g , h ]₁ ⊗₁ id) ⊗₁ id)
        ≈⟨ assoc ⟩
      eval ∘ α⇒ ∘ (([ f ⊗₁ g , h ]₁ ⊗₁ id) ⊗₁ id)
        ≈⟨ refl⟩∘⟨ α⇒-⊗id-commute ⟩
      eval ∘ ([ f ⊗₁ g , h ]₁ ⊗₁ id) ∘ α⇒
        ≈⟨ pullˡ eval-comm ⟩
      (h ∘ eval ∘ (id ⊗₁ (f ⊗₁ g))) ∘ α⇒
        ≈⟨ assoc ⟩
      h ∘ (eval ∘ (id ⊗₁ (f ⊗₁ g))) ∘ α⇒
        ≈⟨ refl⟩∘⟨ assoc ⟩
      h ∘ eval ∘ (id ⊗₁ (f ⊗₁ g)) ∘ α⇒
        ∎
    lhs : uncurry (uncurry ([ f , [ g , h ]₁ ]₁ ∘ curry₂)) ≈ h ∘ eval ∘ (id ⊗₁ (f ⊗₁ g)) ∘ α⇒
    lhs = begin
      uncurry (uncurry ([ f , [ g , h ]₁ ]₁ ∘ curry₂))
        ≈⟨ uncurry-resp-≈ uncurry-∘ ⟩
      uncurry (uncurry [ f , [ g , h ]₁ ]₁ ∘ (curry₂ ⊗₁ id))
        ≈⟨ uncurry-∘ ⟩
      uncurry (uncurry [ f , [ g , h ]₁ ]₁) ∘ ((curry₂ ⊗₁ id) ⊗₁ id)
        ≈⟨ uncurry-resp-≈ eval-comm ⟩∘⟨refl ⟩
      uncurry ([ g , h ]₁ ∘ eval ∘ (id ⊗₁ f)) ∘ ((curry₂ ⊗₁ id) ⊗₁ id)
        ≈⟨ uncurry-∘ ⟩∘⟨refl ⟩
      (uncurry [ g , h ]₁ ∘ ((eval ∘ (id ⊗₁ f)) ⊗₁ id)) ∘ ((curry₂ ⊗₁ id) ⊗₁ id)
        ≈⟨ (eval-comm ⟩∘⟨refl) ⟩∘⟨refl ⟩
      ((h ∘ eval ∘ (id ⊗₁ g)) ∘ ((eval ∘ (id ⊗₁ f)) ⊗₁ id)) ∘ ((curry₂ ⊗₁ id) ⊗₁ id)
        ≈⟨ assoc ⟩
      (h ∘ eval ∘ (id ⊗₁ g)) ∘ (((eval ∘ (id ⊗₁ f)) ⊗₁ id) ∘ ((curry₂ ⊗₁ id) ⊗₁ id))
        ≈⟨ refl⟩∘⟨ merge₁ˡ ⟩
      (h ∘ eval ∘ (id ⊗₁ g)) ∘ (((eval ∘ (id ⊗₁ f)) ∘ (curry₂ ⊗₁ id)) ⊗₁ id)
        ≈⟨ refl⟩∘⟨ (assoc ⟩⊗⟨refl) ⟩
      (h ∘ eval ∘ (id ⊗₁ g)) ∘ ((eval ∘ ((id ⊗₁ f) ∘ (curry₂ ⊗₁ id))) ⊗₁ id)
        ≈⟨ refl⟩∘⟨ ((refl⟩∘⟨ (⟺ whisker-comm)) ⟩⊗⟨refl) ⟩
      (h ∘ eval ∘ (id ⊗₁ g)) ∘ ((eval ∘ ((curry₂ ⊗₁ id) ∘ (id ⊗₁ f))) ⊗₁ id)
        ≈⟨ refl⟩∘⟨ (sym-assoc ⟩⊗⟨refl) ⟩
      (h ∘ eval ∘ (id ⊗₁ g)) ∘ (((eval ∘ (curry₂ ⊗₁ id)) ∘ (id ⊗₁ f)) ⊗₁ id)
        ≈⟨ refl⟩∘⟨ ((eval-curry ⟩∘⟨refl) ⟩⊗⟨refl) ⟩
      (h ∘ eval ∘ (id ⊗₁ g)) ∘ ((curry (eval ∘ α⇒) ∘ (id ⊗₁ f)) ⊗₁ id)
        ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
      (h ∘ eval ∘ (id ⊗₁ g)) ∘ (curry (eval ∘ α⇒) ⊗₁ id) ∘ ((id ⊗₁ f) ⊗₁ id)
        ≈⟨ assoc ⟩
      h ∘ (eval ∘ (id ⊗₁ g)) ∘ (curry (eval ∘ α⇒) ⊗₁ id) ∘ ((id ⊗₁ f) ⊗₁ id)
        ≈⟨ refl⟩∘⟨ core ⟩
      h ∘ eval ∘ (id ⊗₁ (f ⊗₁ g)) ∘ α⇒
        ∎

-- Naturality of `uncurry₂` (the inverse square), by conjugating `curry₂-natural`.
uncurry₂-natural : {f : X ⇒ A} {g : Y ⇒ B} {h : C ⇒ Z} →
  [ f ⊗₁ g , h ]₁ ∘ uncurry₂ ≈ uncurry₂ ∘ [ f , [ g , h ]₁ ]₁
uncurry₂-natural {f = f} {g = g} {h = h} = begin
  [ f ⊗₁ g , h ]₁ ∘ uncurry₂
    ≈˘⟨ cancelˡ curry₂-iso-uncurry₂ ⟩
  uncurry₂ ∘ curry₂ ∘ [ f ⊗₁ g , h ]₁ ∘ uncurry₂
    ≈˘⟨ refl⟩∘⟨ assoc ⟩
  uncurry₂ ∘ (curry₂ ∘ [ f ⊗₁ g , h ]₁) ∘ uncurry₂
    ≈˘⟨ refl⟩∘⟨ curry₂-natural ⟩∘⟨refl ⟩
  uncurry₂ ∘ ([ f , [ g , h ]₁ ]₁ ∘ curry₂) ∘ uncurry₂
    ≈⟨ refl⟩∘⟨ cancelʳ uncurry₂-iso-curry₂ ⟩
  uncurry₂ ∘ [ f , [ g , h ]₁ ]₁
    ∎

------------------------------------------------------------------------
-- `curry₂-iso` as a natural isomorphism.  With `A`, `B`, `C` varying, both sides are
-- trifunctors on `𝒞ᵒᵖ × 𝒞ᵒᵖ × 𝒞`: `F⊗ = [ - ⊗₀ - , - ]₀` and `F² = [ - , [ - , - ]₀ ]₀`.

private
  𝒞ᵒᵖ = Category.op 𝒞

  F⊗ : Functor (Product 𝒞ᵒᵖ (Product 𝒞ᵒᵖ 𝒞)) 𝒞
  F⊗ = [-,-] ∘F ((Functor.op ⊗ ∘F (πˡ ※ (πˡ ∘F πʳ))) ※ (πʳ ∘F πʳ))

  F² : Functor (Product 𝒞ᵒᵖ (Product 𝒞ᵒᵖ 𝒞)) 𝒞
  F² = [-,-] ∘F (idF ⁂ [-,-])

curry₂-NI : NaturalIsomorphism F⊗ F²
curry₂-NI = record
  { F⇒G = ntHelper record { η = λ _ → curry₂ ; commute = λ _ → ⟺ curry₂-natural }
  ; F⇐G = ntHelper record { η = λ _ → uncurry₂ ; commute = λ _ → ⟺ uncurry₂-natural }
  ; iso = λ _ → record { isoˡ = curry₂-iso-uncurry₂ ; isoʳ = uncurry₂-iso-curry₂ }
  }
