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

import Categories.Enriched.Category as Enriched

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
open import Categories.Enriched.Category M using (_[_,_])
open Shorthands

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

-- Uncurrying distributes over precomposition and respects equality.
uncurry-∘ : {g : B ⇒ [ X , Y ]₀} {h : A ⇒ B} →
  uncurry (g ∘ h) ≈ uncurry g ∘ (h ⊗₁ id)
uncurry-∘ = (refl⟩∘⟨ split₁ˡ) ○ sym-assoc

uncurry-resp-≈ : {g h : A ⇒ [ X , Y ]₀} → g ≈ h → uncurry g ≈ uncurry h
uncurry-resp-≈ p = refl⟩∘⟨ (p ⟩⊗⟨refl)

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
abstract
  eval-comm : {p : A ⇒ B} {q : X ⇒ Y} →
    eval {A} {Y} ∘ ([ p , q ]₁ ⊗₁ id) ≈ q ∘ eval ∘ (id ⊗₁ p)
  eval-comm {p = p} {q = q} = begin
    eval ∘ ([ p , q ]₁ ⊗₁ id)                          ≈⟨ refl⟩∘⟨ ([ [-,-] ]-decompose₂ ⟩⊗⟨refl) ⟩
    eval ∘ (([ id , q ]₁ ∘ [ p , id ]₁) ⊗₁ id)         ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
    eval ∘ ([ id , q ]₁ ⊗₁ id) ∘ ([ p , id ]₁ ⊗₁ id)   ≈⟨ pullˡ eval-comm-cod ⟩
    (q ∘ eval) ∘ ([ p , id ]₁ ⊗₁ id)                   ≈⟨ pullʳ eval-comm-dom ⟩
    q ∘ eval ∘ (id ⊗₁ p)                               ∎

-- Evaluating a curried map after reindexing its argument.
eval-curry-reindex : {p : A ⇒ B} {g : C ⊗₀ B ⇒ X} →
  (eval ∘ (id ⊗₁ p)) ∘ (curry g ⊗₁ id) ≈ g ∘ (id ⊗₁ p)
eval-curry-reindex = pullʳ (⟺ whisker-comm) ○ pullˡ eval-curry

-- Hom action on a curried map is precomposition in the argument and
-- postcomposition in the result.
abstract
  hom-curry : {p : A ⇒ B} {q : X ⇒ Y} {g : C ⊗₀ B ⇒ X} →
    [ p , q ]₁ ∘ curry g ≈ curry (q ∘ g ∘ (id ⊗₁ p))
  hom-curry {p = p} {q = q} {g = g} = uncurry-injective (begin
    uncurry ([ p , q ]₁ ∘ curry g)                  ≈⟨ uncurry-∘ ⟩
    (eval ∘ ([ p , q ]₁ ⊗₁ id)) ∘ (curry g ⊗₁ id)  ≈⟨ eval-comm ⟩∘⟨refl ⟩
    (q ∘ eval ∘ (id ⊗₁ p)) ∘ (curry g ⊗₁ id)       ≈⟨ pullʳ eval-curry-reindex ⟩
    q ∘ g ∘ (id ⊗₁ p)                               ≈˘⟨ eval-curry ⟩
    uncurry (curry (q ∘ g ∘ (id ⊗₁ p)))            ∎)

hom-curryᵣ : {p : A ⇒ B} {g : C ⊗₀ B ⇒ X} →
  [ p , id ]₁ ∘ curry g ≈ curry (g ∘ (id ⊗₁ p))
hom-curryᵣ = hom-curry ○ curry-resp-≈ identityˡ

-- Composition of internal-hom actions.
hom-∘ : {a : C ⇒ B} {c : B ⇒ A} {b : Y ⇒ Z} {d : X ⇒ Y} →
  [ a , b ]₁ ∘ [ c , d ]₁ ≈ [ c ∘ a , b ∘ d ]₁
hom-∘ = ⟺ [-,-].homomorphism

hom-∘ᵣ : {a : C ⇒ B} {c : B ⇒ A} → [ a , id {X} ]₁ ∘ [ c , id ]₁ ≈ [ c ∘ a , id ]₁
hom-∘ᵣ = hom-∘ ○ [-,-].F-resp-≈ (Equiv.refl , identity²)

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

⌜⌝-resp-≈ : {f g : X ⇒ Y} → f ≈ g → ⌜ f ⌝ ≈ ⌜ g ⌝
⌜⌝-resp-≈ f≈g = curry-resp-≈ (f≈g ⟩∘⟨refl)

-- Reindexing the domain of a named map is precomposition.
⌜hom⌝ʳ : {f : A ⇒ B} {g : B ⇒ C} → [ f , id ]₁ ∘ ⌜ g ⌝ ≈ ⌜ g ∘ f ⌝
⌜hom⌝ʳ {f = f} {g} = begin
  [ f , id ]₁ ∘ ⌜ g ⌝                    ≈⟨ hom-curryᵣ ⟩
  curry ((g ∘ λ⇒) ∘ (id ⊗₁ f))          ≈⟨ curry-resp-≈ assoc ⟩
  curry (g ∘ λ⇒ ∘ (id ⊗₁ f))            ≈⟨ curry-resp-≈ (refl⟩∘⟨ unitorˡ-commute-from) ⟩
  curry (g ∘ f ∘ λ⇒)                    ≈⟨ curry-resp-≈ sym-assoc ⟩
  ⌜ g ∘ f ⌝                             ∎

-- Reindexing the codomain of a named map is postcomposition.
⌜hom⌝ˡ : {f : A ⇒ B} {g : B ⇒ C} → [ id , g ]₁ ∘ ⌜ f ⌝ ≈ ⌜ g ∘ f ⌝
⌜hom⌝ˡ {f = f} {g} = begin
  [ id , g ]₁ ∘ ⌜ f ⌝                          ≈⟨ hom-curry ⟩
  curry (g ∘ (f ∘ λ⇒) ∘ (id ⊗₁ id))           ≈⟨ curry-resp-≈ (refl⟩∘⟨ refl⟩∘⟨ ⊗.identity) ⟩
  curry (g ∘ (f ∘ λ⇒) ∘ id)                   ≈⟨ curry-resp-≈ (refl⟩∘⟨ identityʳ) ⟩
  curry (g ∘ f ∘ λ⇒)                          ≈⟨ curry-resp-≈ sym-assoc ⟩
  ⌜ g ∘ f ⌝                                   ∎

-- Evaluating a named map after reindexing its argument is ordinary composition.
eval-⌜⌝-at : {f : B ⇒ C} {g : A ⇒ B} →
  eval ∘ (⌜ f ⌝ ⊗₁ g) ≈ (f ∘ λ⇒) ∘ (id ⊗₁ g)
eval-⌜⌝-at {f = f} {g} = begin
  eval ∘ (⌜ f ⌝ ⊗₁ g)                ≈⟨ refl⟩∘⟨ serialize₁₂ ⟩
  eval ∘ (⌜ f ⌝ ⊗₁ id) ∘ (id ⊗₁ g)  ≈⟨ pullˡ eval-⌜⌝ ⟩
  (f ∘ λ⇒) ∘ (id ⊗₁ g)              ∎

eval-⌜⌝-unit : {f : B ⇒ C} {g : A ⇒ B} →
  (eval ∘ (⌜ f ⌝ ⊗₁ g)) ∘ λ⇐ ≈ f ∘ g
eval-⌜⌝-unit = begin
  (eval ∘ (⌜ _ ⌝ ⊗₁ _)) ∘ λ⇐          ≈⟨ eval-⌜⌝-at ⟩∘⟨refl ⟩
  (( _ ∘ λ⇒) ∘ (id ⊗₁ _)) ∘ λ⇐        ≈⟨ pullʳ (⟺ unitorˡ-commute-to) ⟩
  (_ ∘ λ⇒) ∘ λ⇐ ∘ _                   ≈⟨ cancelInner unitorˡ.isoʳ ⟩
  _ ∘ _                               ∎

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

abstract
  internal-∘-curry : {f : A ⊗₀ Y ⇒ Z} {g : B ⊗₀ X ⇒ Y} →
    internal-∘ ∘ (curry f ⊗₁ curry g) ≈ curry (f ∘ (id ⊗₁ g) ∘ α⇒)
  internal-∘-curry {f = f} {g = g} = uncurry-injective (begin
    uncurry (internal-∘ ∘ (curry f ⊗₁ curry g))               ≈⟨ uncurry-∘ ⟩
    uncurry internal-∘ ∘ ((curry f ⊗₁ curry g) ⊗₁ id)         ≈⟨ eval-internal-∘ ⟩∘⟨refl ⟩
    (eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ ((curry f ⊗₁ curry g) ⊗₁ id)
      ≈⟨ pull-last assoc-commute-from ⟩
    eval ∘ (id ⊗₁ eval) ∘ (curry f ⊗₁ (curry g ⊗₁ id)) ∘ α⇒   ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
    eval ∘ (curry f ⊗₁ (eval ∘ (curry g ⊗₁ id))) ∘ α⇒         ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ eval-curry) ⟩∘⟨refl ⟩
    eval ∘ (curry f ⊗₁ g) ∘ α⇒                                ≈⟨ refl⟩∘⟨ pushˡ serialize₁₂ ⟩
    eval ∘ (curry f ⊗₁ id) ∘ (id ⊗₁ g) ∘ α⇒                   ≈⟨ pullˡ eval-curry ⟩
    f ∘ (id ⊗₁ g) ∘ α⇒                                        ≈˘⟨ eval-curry ⟩
    uncurry (curry (f ∘ (id ⊗₁ g) ∘ α⇒))                      ∎)

  internal-∘-curry′ : (f : A ⇒ [ Y , Z ]₀) (g : B ⇒ [ X , Y ]₀) →
    internal-∘ {Y = Y} ∘ (f ⊗₁ g) ≈ curry (uncurry f ∘ (id ⊗₁ uncurry g) ∘ α⇒)
  internal-∘-curry′ f g = begin
    internal-∘ ∘ (f ⊗₁ g)                                  ≈˘⟨ refl⟩∘⟨ curry-eval ⟩⊗⟨ curry-eval ⟩
    internal-∘ ∘ (curry (uncurry f) ⊗₁ curry (uncurry g))  ≈⟨ internal-∘-curry ⟩
    curry (uncurry f ∘ (id ⊗₁ uncurry g) ∘ α⇒)             ∎

-- Composing with an internal identity does nothing.  Both unit laws are proved by
-- uncurrying: the whiskered `j` meets `ev` and unfolds to a unitor.

abstract
  internal-∘-idˡ : internal-∘ {X = X} ∘ (⌜id⌝ {Y} ⊗₁ id) ≈ λ⇒
  internal-∘-idˡ = uncurry-injective (begin
    eval ∘ ((internal-∘ ∘ (⌜id⌝ ⊗₁ id)) ⊗₁ id)          ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
    eval ∘ (internal-∘ ⊗₁ id) ∘ ((⌜id⌝ ⊗₁ id) ⊗₁ id)    ≈⟨ pullˡ eval-internal-∘ ⟩
    (eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ ((⌜id⌝ ⊗₁ id) ⊗₁ id)   ≈⟨ pull-last α⇒-⊗id-commute ⟩
    eval ∘ (id ⊗₁ eval) ∘ (⌜id⌝ ⊗₁ id) ∘ α⇒             ≈⟨ refl⟩∘⟨ extendʳ (⟺ whisker-comm) ⟩
    eval ∘ (⌜id⌝ ⊗₁ id) ∘ (id ⊗₁ eval) ∘ α⇒             ≈⟨ pullˡ eval-⌜id⌝ ⟩
    λ⇒ ∘ (id ⊗₁ eval) ∘ α⇒                              ≈⟨ pullˡ unitorˡ-commute-from ⟩
    (eval ∘ λ⇒) ∘ α⇒                                    ≈⟨ pullʳ coherence₁ ⟩
    eval ∘ (λ⇒ ⊗₁ id)                                   ∎)

  internal-∘-idʳ : internal-∘ {Y = X} {Z = Z} ∘ (id ⊗₁ ⌜id⌝ {X}) ≈ ρ⇒
  internal-∘-idʳ = uncurry-injective (begin
    eval ∘ ((internal-∘ ∘ (id ⊗₁ ⌜id⌝)) ⊗₁ id)          ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
    eval ∘ (internal-∘ ⊗₁ id) ∘ ((id ⊗₁ ⌜id⌝) ⊗₁ id)    ≈⟨ pullˡ eval-internal-∘ ⟩
    (eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ ((id ⊗₁ ⌜id⌝) ⊗₁ id)   ≈⟨ pull-last assoc-commute-from ⟩
    eval ∘ (id ⊗₁ eval) ∘ (id ⊗₁ (⌜id⌝ ⊗₁ id)) ∘ α⇒     ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
    eval ∘ (id ⊗₁ (eval ∘ (⌜id⌝ ⊗₁ id))) ∘ α⇒           ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ eval-⌜id⌝) ⟩∘⟨refl ⟩
    eval ∘ (id ⊗₁ λ⇒) ∘ α⇒                              ≈⟨ refl⟩∘⟨ triangle ⟩
    eval ∘ (ρ⇒ ⊗₁ id)                                   ∎)

-- Associativity of internal composition.
internal-∘-assoc :
    internal-∘ {B} {Z} {A} ∘ (internal-∘ {C} {Z} {B} ⊗₁ id)
  ≈ internal-∘ {C} {Z} {A} ∘ (id ⊗₁ internal-∘ {B} {C} {A}) ∘ α⇒
internal-∘-assoc = uncurry-injective (begin
    uncurry (internal-∘ ∘ (internal-∘ ⊗₁ id))  ≈⟨ uncurry-∘ ⟩
    uncurry internal-∘ ∘ ((internal-∘ ⊗₁ id) ⊗₁ id)
      ≈⟨ eval-internal-∘ ⟩∘⟨refl ⟩
    (eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ ((internal-∘ ⊗₁ id) ⊗₁ id)
      ≈⟨ pull-last assoc-commute-from ⟩
    eval ∘ (id ⊗₁ eval) ∘ (internal-∘ ⊗₁ (id ⊗₁ id)) ∘ α⇒
      ≈⟨ refl⟩∘⟨ pullˡ evaluation-interchange ⟩
    eval ∘ ((internal-∘ ⊗₁ id) ∘ (id ⊗₁ eval)) ∘ α⇒
      ≈⟨ refl⟩∘⟨ assoc ⟩
    eval ∘ (internal-∘ ⊗₁ id) ∘ (id ⊗₁ eval) ∘ α⇒  ≈⟨ pullˡ eval-internal-∘ ⟩
    (eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ (id ⊗₁ eval) ∘ α⇒  ≈⟨ assoc²βε ⟩
    eval ∘ (id ⊗₁ eval) ∘ α⇒ ∘ (id ⊗₁ eval) ∘ α⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ α⇒-id⊗-commute ⟩
    eval ∘ (id ⊗₁ eval) ∘ ((id ⊗₁ (id ⊗₁ eval)) ∘ α⇒) ∘ α⇒
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
    eval ∘ (id ⊗₁ eval) ∘ (id ⊗₁ (id ⊗₁ eval)) ∘ α⇒ ∘ α⇒
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pentagon ⟩
    eval ∘ (id ⊗₁ eval) ∘ (id ⊗₁ (id ⊗₁ eval)) ∘ (id ⊗₁ α⇒)
      ∘ α⇒ ∘ (α⇒ ⊗₁ id)
      ≈˘⟨ refl⟩∘⟨ expand-nested-evaluation ⟩
    eval ∘ (id ⊗₁ (eval ∘ (id ⊗₁ eval) ∘ α⇒)) ∘ α⇒ ∘ (α⇒ ⊗₁ id)
      ≈˘⟨ refl⟩∘⟨ (refl⟩⊗⟨ eval-internal-∘) ⟩∘⟨refl ⟩
    eval ∘ (id ⊗₁ uncurry internal-∘) ∘ α⇒ ∘ (α⇒ ⊗₁ id)
      ≈˘⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
    eval ∘ (id ⊗₁ eval) ∘ (id ⊗₁ (internal-∘ ⊗₁ id)) ∘ α⇒ ∘ (α⇒ ⊗₁ id)
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
    eval ∘ (id ⊗₁ eval) ∘ ((id ⊗₁ (internal-∘ ⊗₁ id)) ∘ α⇒) ∘ (α⇒ ⊗₁ id)
      ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ assoc-commute-from ⟩
    eval ∘ (id ⊗₁ eval) ∘ α⇒ ∘ ((id ⊗₁ internal-∘) ⊗₁ id) ∘ (α⇒ ⊗₁ id)
      ≈˘⟨ assoc²βε ⟩
    (eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ ((id ⊗₁ internal-∘) ⊗₁ id) ∘ (α⇒ ⊗₁ id)
      ≈˘⟨ refl⟩∘⟨ split₁ˡ ⟩
    (eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ (((id ⊗₁ internal-∘) ∘ α⇒) ⊗₁ id)
      ≈˘⟨ eval-internal-∘ ⟩∘⟨refl ⟩
    uncurry internal-∘ ∘ (((id ⊗₁ internal-∘) ∘ α⇒) ⊗₁ id)  ≈˘⟨ uncurry-∘ ⟩
    uncurry (internal-∘ ∘ (id ⊗₁ internal-∘) ∘ α⇒)  ∎)
    where
      evaluation-interchange :
        (id ⊗₁ eval) ∘ (internal-∘ ⊗₁ (id ⊗₁ id))
          ≈ (internal-∘ ⊗₁ id) ∘ (id ⊗₁ eval)
      evaluation-interchange = begin
        (id ⊗₁ eval) ∘ (internal-∘ ⊗₁ (id ⊗₁ id))  ≈⟨ ⟺ ⊗.homomorphism ⟩
        (id ∘ internal-∘) ⊗₁ (eval ∘ (id ⊗₁ id))    ≈⟨ identityˡ ⟩⊗⟨ elimʳ ⊗.identity ⟩
        internal-∘ ⊗₁ eval                            ≈⟨ serialize₁₂ ⟩
        (internal-∘ ⊗₁ id) ∘ (id ⊗₁ eval)            ∎

      expand-nested-evaluation :
        (id ⊗₁ (eval ∘ (id ⊗₁ eval) ∘ α⇒)) ∘ α⇒ ∘ (α⇒ ⊗₁ id)
          ≈ (id ⊗₁ eval) ∘ (id ⊗₁ (id ⊗₁ eval)) ∘ (id ⊗₁ α⇒)
            ∘ α⇒ ∘ (α⇒ ⊗₁ id)
      expand-nested-evaluation = begin
        (id ⊗₁ (eval ∘ (id ⊗₁ eval) ∘ α⇒)) ∘ (α⇒ ∘ (α⇒ ⊗₁ id))
          ≈⟨ split₂³ ⟩∘⟨refl ⟩
        ((id ⊗₁ eval) ∘ (id ⊗₁ (id ⊗₁ eval)) ∘ (id ⊗₁ α⇒))
          ∘ (α⇒ ∘ (α⇒ ⊗₁ id))
          ≈⟨ assoc²βε ⟩
        (id ⊗₁ eval) ∘ (id ⊗₁ (id ⊗₁ eval)) ∘ (id ⊗₁ α⇒)
          ∘ α⇒ ∘ (α⇒ ⊗₁ id)  ∎

------------------------------------------------------------------------
-- The canonical self-enrichment and its ordinary hom-set bridge.

selfEnrichment : Enriched.Category M o
selfEnrichment = record
  { Obj = Obj
  ; hom = [_,_]₀
  ; id = ⌜id⌝
  ; ⊚ = internal-∘
  ; ⊚-assoc = internal-∘-assoc
  ; unitˡ = internal-∘-idˡ
  ; unitʳ = internal-∘-idʳ
  }

⌞_⌟ᶜ : (unit ⇒ [ A , B ]₀) → A ⇒ B
⌞ f ⌟ᶜ = uncurry f ∘ λ⇐

⌞⌜⌝⌟ᶜ : {f : A ⇒ B} → ⌞ ⌜ f ⌝ ⌟ᶜ ≈ f
⌞⌜⌝⌟ᶜ {f = f} = begin
  uncurry ⌜ f ⌝ ∘ λ⇐  ≈⟨ eval-⌜⌝ ⟩∘⟨refl ⟩
  (f ∘ λ⇒) ∘ λ⇐      ≈⟨ cancelʳ unitorˡ.isoʳ ⟩
  f                   ∎

⌜⌞⌟⌝ᶜ : {f : unit ⇒ [ A , B ]₀} → ⌜ ⌞ f ⌟ᶜ ⌝ ≈ f
⌜⌞⌟⌝ᶜ {f = f} = uncurry-injective (begin
  uncurry ⌜ uncurry f ∘ λ⇐ ⌝  ≈⟨ eval-⌜⌝ ⟩
  (uncurry f ∘ λ⇐) ∘ λ⇒      ≈⟨ cancelʳ unitorˡ.isoˡ ⟩
  uncurry f                   ∎)

-- Applying an internal map to the name of `g` is ordinary precomposition by `g`.
uncurry-∘-⌜⌝ʳ : {f : W ⇒ [ B , C ]₀} {g : A ⇒ B} →
  uncurry (internal-∘ ∘ (f ⊗₁ ⌜ g ⌝) ∘ ρ⇐) ≈ uncurry f ∘ (id ⊗₁ g)
uncurry-∘-⌜⌝ʳ {f = f} {g} = begin
  uncurry (internal-∘ ∘ (f ⊗₁ ⌜ g ⌝) ∘ ρ⇐)
    ≈⟨ uncurry-resp-≈ sym-assoc ⟩
  uncurry ((internal-∘ ∘ (f ⊗₁ ⌜ g ⌝)) ∘ ρ⇐)
    ≈⟨ uncurry-∘ ⟩
  uncurry (internal-∘ ∘ (f ⊗₁ ⌜ g ⌝)) ∘ (ρ⇐ ⊗₁ id)
    ≈⟨ uncurry-resp-≈ (internal-∘-curry′ f ⌜ g ⌝) ⟩∘⟨refl ⟩
  uncurry (curry (uncurry f ∘ (id ⊗₁ uncurry ⌜ g ⌝) ∘ α⇒)) ∘ (ρ⇐ ⊗₁ id)
    ≈⟨ eval-curry ⟩∘⟨refl ⟩
  (uncurry f ∘ (id ⊗₁ uncurry ⌜ g ⌝) ∘ α⇒) ∘ (ρ⇐ ⊗₁ id)
    ≈⟨ assoc²βε ⟩
  uncurry f ∘ (id ⊗₁ uncurry ⌜ g ⌝) ∘ α⇒ ∘ (ρ⇐ ⊗₁ id)
    ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ eval-⌜⌝) ⟩∘⟨refl ⟩
  uncurry f ∘ (id ⊗₁ (g ∘ λ⇒)) ∘ α⇒ ∘ (ρ⇐ ⊗₁ id)
    ≈⟨ refl⟩∘⟨ pushˡ split₂ʳ ⟩
  uncurry f ∘ (id ⊗₁ g) ∘ ((id ⊗₁ λ⇒) ∘ α⇒ ∘ (ρ⇐ ⊗₁ id))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ triangle ⟩
  uncurry f ∘ (id ⊗₁ g) ∘ ((ρ⇒ ⊗₁ id) ∘ (ρ⇐ ⊗₁ id))
    ≈⟨ refl⟩∘⟨ elimʳ (⊗-cancel unitorʳ.isoʳ identity²) ⟩
  uncurry f ∘ (id ⊗₁ g)  ∎

-- Applying the name of `g` on the left is ordinary postcomposition by `g`.
uncurry-∘-⌜⌝ˡ : {f : W ⇒ [ A , B ]₀} {g : B ⇒ C} →
  uncurry (internal-∘ ∘ (⌜ g ⌝ ⊗₁ f) ∘ λ⇐) ≈ g ∘ uncurry f
uncurry-∘-⌜⌝ˡ {W = W} {A = A} {f = f} {g} = begin
  uncurry (internal-∘ ∘ (⌜ g ⌝ ⊗₁ f) ∘ λ⇐)
    ≈⟨ uncurry-resp-≈ sym-assoc ⟩
  uncurry ((internal-∘ ∘ (⌜ g ⌝ ⊗₁ f)) ∘ λ⇐)
    ≈⟨ uncurry-∘ ⟩
  uncurry (internal-∘ ∘ (⌜ g ⌝ ⊗₁ f)) ∘ (λ⇐ ⊗₁ id)
    ≈⟨ uncurry-resp-≈ (internal-∘-curry′ ⌜ g ⌝ f) ⟩∘⟨refl ⟩
  uncurry (curry (uncurry ⌜ g ⌝ ∘ (id ⊗₁ uncurry f) ∘ α⇒)) ∘ (λ⇐ ⊗₁ id)
    ≈⟨ eval-curry ⟩∘⟨refl ⟩
  (uncurry ⌜ g ⌝ ∘ (id ⊗₁ uncurry f) ∘ α⇒) ∘ (λ⇐ ⊗₁ id)
    ≈⟨ assoc²βε ⟩
  uncurry ⌜ g ⌝ ∘ (id ⊗₁ uncurry f) ∘ α⇒ ∘ (λ⇐ ⊗₁ id)
    ≈⟨ eval-⌜⌝ ⟩∘⟨refl ⟩
  (g ∘ λ⇒) ∘ (id ⊗₁ uncurry f) ∘ α⇒ ∘ (λ⇐ ⊗₁ id)
    ≈⟨ pullʳ unit-parameter ⟩
  g ∘ uncurry f  ∎
  where
    unit-parameter : λ⇒ ∘ (id ⊗₁ uncurry f) ∘ α⇒ ∘ (λ⇐ {W} ⊗₁ id {A}) ≈ uncurry f
    unit-parameter = begin
      λ⇒ ∘ (id ⊗₁ uncurry f) ∘ α⇒ ∘ (λ⇐ ⊗₁ id)
        ≈⟨ pullˡ unitorˡ-commute-from ⟩
      (uncurry f ∘ λ⇒) ∘ α⇒ ∘ (λ⇐ ⊗₁ id)  ≈⟨ assoc ⟩
      uncurry f ∘ λ⇒ ∘ α⇒ ∘ (λ⇐ ⊗₁ id)
        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ λ⇐-assoc ⟩
      uncurry f ∘ λ⇒ ∘ λ⇐  ≈⟨ elimʳ unitorˡ.isoʳ ⟩
      uncurry f  ∎

-- Composition in the underlying self-enrichment is naming ordinary composition.
⌜∘⌝ : {f : B ⇒ C} {g : A ⇒ B} →
  internal-∘ ∘ (⌜ f ⌝ ⊗₁ ⌜ g ⌝) ∘ λ⇐ ≈ ⌜ f ∘ g ⌝
⌜∘⌝ {f = f} {g} = uncurry-injective (begin
  uncurry (internal-∘ ∘ (⌜ f ⌝ ⊗₁ ⌜ g ⌝) ∘ λ⇐)
    ≈⟨ uncurry-∘-⌜⌝ˡ ⟩
  f ∘ uncurry ⌜ g ⌝  ≈⟨ refl⟩∘⟨ eval-⌜⌝ ⟩
  f ∘ g ∘ λ⇒         ≈˘⟨ assoc ⟩
  (f ∘ g) ∘ λ⇒       ≈˘⟨ eval-⌜⌝ ⟩
  uncurry ⌜ f ∘ g ⌝  ∎)

abstract
  uncurry²-∘-⌜⌝ʳ : {f : W ⇒ [ B , [ C , Z ]₀ ]₀} {g : A ⇒ B} →
    uncurry (uncurry (internal-∘ ∘ (f ⊗₁ ⌜ g ⌝) ∘ ρ⇐))
    ≈ uncurry (uncurry f) ∘ ((id ⊗₁ g) ⊗₁ id)
  uncurry²-∘-⌜⌝ʳ {f = f} {g} = begin
    uncurry (uncurry (internal-∘ ∘ (f ⊗₁ ⌜ g ⌝) ∘ ρ⇐))
      ≈⟨ uncurry-resp-≈ uncurry-∘-⌜⌝ʳ ⟩
    uncurry (uncurry f ∘ (id ⊗₁ g))  ≈⟨ uncurry-∘ ⟩
    uncurry (uncurry f) ∘ ((id ⊗₁ g) ⊗₁ id)  ∎

------------------------------------------------------------------------
-- `unit-hom : X ≅ [ unit , X ]₀`.  A function of no arguments is a value.

unit-hom⇒ : X ⇒ [ unit , X ]₀
unit-hom⇒ = curry ρ⇒

unit-hom⇐ : [ unit , X ]₀ ⇒ X
unit-hom⇐ = eval ∘ ρ⇐

unit-hom⇐-natural : {f : X ⇒ Y} → unit-hom⇐ ∘ [ id , f ]₁ ≈ f ∘ unit-hom⇐
unit-hom⇐-natural {f = f} = begin
  (eval ∘ ρ⇐) ∘ [ id , f ]₁        ≈⟨ pullʳ unitorʳ-commute-to ⟩
  eval ∘ ([ id , f ]₁ ⊗₁ id) ∘ ρ⇐  ≈⟨ pullˡ eval-comm-cod ⟩
  (f ∘ eval) ∘ ρ⇐                  ≈⟨ assoc ⟩
  f ∘ unit-hom⇐                    ∎

eval-unit-hom⇒ : uncurry (unit-hom⇒ {X}) ≈ ρ⇒
eval-unit-hom⇒ = eval-curry

abstract
  unit-hom-isoˡ : unit-hom⇐ ∘ unit-hom⇒ ≈ id {X}
  unit-hom-isoˡ = begin
    (eval ∘ ρ⇐) ∘ unit-hom⇒        ≈⟨ pullʳ unitorʳ-commute-to ⟩
    eval ∘ (unit-hom⇒ ⊗₁ id) ∘ ρ⇐  ≈⟨ pullˡ eval-unit-hom⇒ ⟩
    ρ⇒ ∘ ρ⇐                        ≈⟨ unitorʳ.isoʳ ⟩
    id                             ∎

  unit-hom-isoʳ : unit-hom⇒ ∘ unit-hom⇐ ≈ id {[ unit , X ]₀}
  unit-hom-isoʳ = uncurry-injective (begin
    eval ∘ ((unit-hom⇒ ∘ unit-hom⇐) ⊗₁ id)          ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
    eval ∘ (unit-hom⇒ ⊗₁ id) ∘ (unit-hom⇐ ⊗₁ id)    ≈⟨ pullˡ eval-unit-hom⇒ ⟩
    ρ⇒ ∘ (unit-hom⇐ ⊗₁ id)                          ≈⟨ unitorʳ-commute-from ⟩
    unit-hom⇐ ∘ ρ⇒                                  ≈⟨ cancelʳ unitorʳ.isoˡ ⟩
    eval                                            ≈˘⟨ elimʳ ⊗.identity ⟩
    eval ∘ (id ⊗₁ id)                               ∎)

unit-hom : X ≅ [ unit , X ]₀
unit-hom = record { from = unit-hom⇒ ; to = unit-hom⇐ ; iso = record { isoˡ = unit-hom-isoˡ ; isoʳ = unit-hom-isoʳ } }

------------------------------------------------------------------------
-- The unit's own hom object, `[ unit , unit ]₀`, is the unit: `j` and `i⇐` are
-- mutually inverse there.  (`i-isoʳ` already gives one half.)

⌜id⌝≈unit-hom⇒ : ⌜id⌝ {unit} ≈ unit-hom⇒
⌜id⌝≈unit-hom⇒ = uncurry-injective (begin
  uncurry (⌜id⌝ {unit})             ≈⟨ eval-⌜id⌝ ⟩
  λ⇒                                ≈⟨ coherence₃ ⟩
  ρ⇒                                ≈˘⟨ eval-unit-hom⇒ ⟩
  uncurry unit-hom⇒                 ∎)

unit-hom⇐-⌜id⌝ : unit-hom⇐ ∘ ⌜id⌝ {unit} ≈ id
unit-hom⇐-⌜id⌝ = begin
  unit-hom⇐ ∘ ⌜id⌝        ≈⟨ refl⟩∘⟨ ⌜id⌝≈unit-hom⇒ ⟩
  unit-hom⇐ ∘ unit-hom⇒   ≈⟨ unit-hom-isoˡ ⟩
  id                      ∎

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

abstract
  internal-∘-unit-hom : unit-hom⇐ ∘ internal-∘ {Y} {Z} {unit} ∘ (id ⊗₁ unit-hom⇒) ≈ eval
  internal-∘-unit-hom = begin
    (eval ∘ ρ⇐) ∘ internal-∘ ∘ (id ⊗₁ unit-hom⇒)                    ≈⟨ center unitorʳ-commute-to ⟩
    eval ∘ (((internal-∘ ⊗₁ id) ∘ ρ⇐) ∘ (id ⊗₁ unit-hom⇒))
      ≈⟨ refl⟩∘⟨ pullʳ unitorʳ-commute-to ⟩
    eval ∘ (internal-∘ ⊗₁ id) ∘ ((id ⊗₁ unit-hom⇒) ⊗₁ id) ∘ ρ⇐      ≈⟨ pullˡ eval-internal-∘ ⟩
    (eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ ((id ⊗₁ unit-hom⇒) ⊗₁ id) ∘ ρ⇐   ≈⟨ assoc²βε ⟩
    eval ∘ (id ⊗₁ eval) ∘ α⇒ ∘ ((id ⊗₁ unit-hom⇒) ⊗₁ id) ∘ ρ⇐
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟩
    eval ∘ (id ⊗₁ eval) ∘ (id ⊗₁ (unit-hom⇒ ⊗₁ id)) ∘ α⇒ ∘ ρ⇐     ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
    eval ∘ (id ⊗₁ (eval ∘ (unit-hom⇒ ⊗₁ id))) ∘ α⇒ ∘ ρ⇐           ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ eval-unit-hom⇒) ⟩∘⟨refl ⟩
    eval ∘ (id ⊗₁ ρ⇒) ∘ α⇒ ∘ ρ⇐                                  ≈⟨ refl⟩∘⟨ pullˡ ρ⇒-α⇒ ⟩
    eval ∘ ρ⇒ ∘ ρ⇐                                                ≈⟨ elimʳ unitorʳ.isoʳ ⟩
    eval                                                          ∎
