{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)

module Categories.Category.Monoidal.Closed.Currying
  {o ℓ e} {𝒞 : Category o ℓ e} {M : Monoidal 𝒞} (Cl : Closed M) where

open Closed Cl using ([_,_]₀; [_,_]₁)

open Category 𝒞
open Monoidal M
open import Categories.Category.Monoidal.Closed.Properties Cl
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Utilities M
open import Categories.Category.Monoidal.Reassociation M
open import Categories.Morphism 𝒞 using (_≅_)
open import Categories.Morphism.Reasoning 𝒞
open Shorthands

private
  variable
    A B C : Obj -- closed arguments
    W X Y Z : Obj -- source, comparison, and codomain roles

------------------------------------------------------------------------
-- Iterated currying.

-- A function of a pair is a function returning a function.  The associators
-- compare `(W ⊗₀ A) ⊗₀ B` with `W ⊗₀ (A ⊗₀ B)`.
curry₂ : [ A ⊗₀ B , C ]₀ ⇒ [ A , [ B , C ]₀ ]₀
curry₂ = curry (curry (eval ∘ α⇒))

uncurry₂ : [ A , [ B , C ]₀ ]₀ ⇒ [ A ⊗₀ B , C ]₀
uncurry₂ = curry (uncurry eval ∘ α⇐)

abstract
  curry₂-iso-uncurry₂ : uncurry₂ {A} {B} {C} ∘ curry₂ ≈ id
  curry₂-iso-uncurry₂ = uncurry-injective (begin
    uncurry (uncurry₂ ∘ curry₂)                        ≈⟨ uncurry-∘ ⟩
    uncurry uncurry₂ ∘ (curry₂ ⊗₁ id)                  ≈⟨ eval-curry ⟩∘⟨refl ⟩
    (uncurry eval ∘ α⇐) ∘ (curry₂ ⊗₁ id)               ≈⟨ assoc ⟩
    uncurry eval ∘ α⇐ ∘ (curry₂ ⊗₁ id)                 ≈⟨ refl⟩∘⟨ α⇐-⊗id-commute ⟩
    uncurry eval ∘ ((curry₂ ⊗₁ id) ⊗₁ id) ∘ α⇐         ≈⟨ sym-assoc ⟩
    (uncurry eval ∘ ((curry₂ ⊗₁ id) ⊗₁ id)) ∘ α⇐       ≈˘⟨ uncurry-∘ ⟩∘⟨refl ⟩
    uncurry (eval ∘ (curry₂ ⊗₁ id)) ∘ α⇐               ≈⟨ uncurry-resp-≈ eval-curry ⟩∘⟨refl ⟩
    uncurry (curry (eval ∘ α⇒)) ∘ α⇐                   ≈⟨ eval-curry ⟩∘⟨refl ⟩
    (eval ∘ α⇒) ∘ α⇐                                   ≈⟨ cancelʳ associator.isoʳ ⟩
    eval                                                ≈˘⟨ elimʳ ⊗.identity ⟩
    eval ∘ (id ⊗₁ id)                                  ∎)

-- Two maps into a doubly iterated hom object agree when their uncurrying does.
uncurry²-injective : {g h : W ⇒ [ A , [ B , C ]₀ ]₀} →
  uncurry (uncurry g) ≈ uncurry (uncurry h) → g ≈ h
uncurry²-injective p = uncurry-injective (uncurry-injective p)

uncurry²-∘ : {g : A ⇒ [ B , [ C , Z ]₀ ]₀} {f : W ⇒ A} →
  uncurry (uncurry (g ∘ f)) ≈ uncurry (uncurry g) ∘ ((f ⊗₁ id) ⊗₁ id)
uncurry²-∘ = uncurry-resp-≈ uncurry-∘ ○ uncurry-∘

abstract
  uncurry₂-iso-curry₂ : curry₂ {A} {B} {C} ∘ uncurry₂ ≈ id
  uncurry₂-iso-curry₂ = uncurry²-injective (begin
    uncurry (uncurry (curry₂ ∘ uncurry₂))               ≈⟨ uncurry-resp-≈ uncurry-∘ ⟩
    uncurry (uncurry curry₂ ∘ (uncurry₂ ⊗₁ id))         ≈⟨ uncurry-∘ ⟩
    uncurry (uncurry curry₂) ∘ ((uncurry₂ ⊗₁ id) ⊗₁ id)
      ≈⟨ uncurry-resp-≈ eval-curry ⟩∘⟨refl ⟩
    uncurry (curry (eval ∘ α⇒)) ∘ ((uncurry₂ ⊗₁ id) ⊗₁ id)  ≈⟨ eval-curry ⟩∘⟨refl ⟩
    (eval ∘ α⇒) ∘ ((uncurry₂ ⊗₁ id) ⊗₁ id)              ≈⟨ pullʳ α⇒-⊗id-commute ⟩
    eval ∘ (uncurry₂ ⊗₁ id) ∘ α⇒                        ≈⟨ pullˡ eval-curry ⟩
    (uncurry eval ∘ α⇐) ∘ α⇒                            ≈⟨ cancelʳ associator.isoˡ ⟩
    uncurry eval                                        ≈˘⟨ uncurry-resp-≈ (elimʳ ⊗.identity) ⟩
    uncurry (eval ∘ (id ⊗₁ id))                         ∎)

curry₂-iso : [ A ⊗₀ B , C ]₀ ≅ [ A , [ B , C ]₀ ]₀
curry₂-iso = record
  { from = curry₂
  ; to = uncurry₂
  ; iso = record { isoˡ = curry₂-iso-uncurry₂ ; isoʳ = uncurry₂-iso-curry₂ }
  }

private
  unit-curry₂-eval : curry (eval {unit ⊗₀ A} {B} ∘ α⇒) ∘ ρ⇐
                       ≈ [ λ⇐ {A} , id ]₁
  unit-curry₂-eval = uncurry-injective (begin
    uncurry (curry (eval ∘ α⇒) ∘ ρ⇐)           ≈⟨ uncurry-∘ ⟩
    uncurry (curry (eval ∘ α⇒)) ∘ (ρ⇐ ⊗₁ id)   ≈⟨ eval-curry ⟩∘⟨refl ⟩
    (eval ∘ α⇒) ∘ (ρ⇐ ⊗₁ id)                   ≈⟨ pullʳ triangle-inv′ ⟩
    eval ∘ (id ⊗₁ λ⇐)                          ≈˘⟨ eval-comm-dom ⟩
    uncurry [ λ⇐ , id ]₁                       ∎)

unit-hom⇐-curry₂ : unit-hom⇐ ∘ curry₂ {unit} {A} {B} ≈ [ λ⇐ {A} , id ]₁
unit-hom⇐-curry₂ = begin
  (eval ∘ ρ⇐) ∘ curry₂           ≈⟨ pullʳ unitorʳ-commute-to ⟩
  eval ∘ (curry₂ ⊗₁ id) ∘ ρ⇐     ≈⟨ pullˡ eval-curry ⟩
  curry (eval ∘ α⇒) ∘ ρ⇐         ≈⟨ unit-curry₂-eval ⟩
  [ λ⇐ , id ]₁                   ∎

-- Double beta for `curry₂`.
uncurry²-curry₂ : uncurry (uncurry (curry₂ {A} {B} {C})) ≈ eval ∘ α⇒
uncurry²-curry₂ = uncurry-resp-≈ eval-curry ○ eval-curry

-- Double uncurrying consumes an immediately preceding `curry₂`.
abstract
  uncurry²-curry₂-∘ : {f : W ⇒ [ A ⊗₀ B , C ]₀} →
    uncurry (uncurry (curry₂ ∘ f)) ≈ uncurry f ∘ α⇒ {W} {A} {B}
  uncurry²-curry₂-∘ {f = f} = begin
    uncurry (uncurry (curry₂ ∘ f))                       ≈⟨ uncurry²-∘ ⟩
    uncurry (uncurry curry₂) ∘ ((f ⊗₁ id) ⊗₁ id)         ≈⟨ uncurry²-curry₂ ⟩∘⟨refl ⟩
    (eval ∘ α⇒) ∘ ((f ⊗₁ id) ⊗₁ id)                     ≈⟨ extendˡ α⇒-⊗id-commute ⟩
    uncurry f ∘ α⇒                                       ∎

-- Naturality of the iterated currying isomorphism.
abstract
  curry₂-natural : {f : X ⇒ A} {g : Y ⇒ B} {h : C ⇒ Z} →
    [ f , [ g , h ]₁ ]₁ ∘ curry₂ ≈ curry₂ ∘ [ f ⊗₁ g , h ]₁
  curry₂-natural {f = f} {g} {h} = uncurry²-injective (begin
    uncurry (uncurry ([ f , [ g , h ]₁ ]₁ ∘ curry₂))
      ≈⟨ uncurry-resp-≈ (uncurry-resp-≈ hom-curry) ⟩
    uncurry (uncurry (curry ([ g , h ]₁ ∘ curry (eval ∘ α⇒) ∘ (id ⊗₁ f))))
      ≈⟨ uncurry-resp-≈ eval-curry ⟩
    uncurry ([ g , h ]₁ ∘ curry (eval ∘ α⇒) ∘ (id ⊗₁ f))
      ≈⟨ uncurry-resp-≈ (pullˡ hom-curry) ⟩
    uncurry (curry (h ∘ (eval ∘ α⇒) ∘ (id ⊗₁ g)) ∘ (id ⊗₁ f))
      ≈⟨ uncurry-∘ ⟩
    uncurry (curry (h ∘ (eval ∘ α⇒) ∘ (id ⊗₁ g))) ∘ ((id ⊗₁ f) ⊗₁ id)
      ≈⟨ eval-curry ⟩∘⟨refl ⟩
    (h ∘ (eval ∘ α⇒) ∘ (id ⊗₁ g)) ∘ ((id ⊗₁ f) ⊗₁ id)  ≈⟨ assoc²βε ⟩
    h ∘ (eval ∘ α⇒) ∘ ((id ⊗₁ g) ∘ ((id ⊗₁ f) ⊗₁ id))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ merge₂ˡ ⟩
    h ∘ (eval ∘ α⇒) ∘ ((id ⊗₁ f) ⊗₁ (g ∘ id))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩⊗⟨ identityʳ ⟩
    h ∘ (eval ∘ α⇒) ∘ ((id ⊗₁ f) ⊗₁ g)  ≈⟨ refl⟩∘⟨ pullʳ assoc-commute-from ⟩
    h ∘ eval ∘ (id ⊗₁ (f ⊗₁ g)) ∘ α⇒              ≈⟨ assoc²εβ ⟩
    (h ∘ eval ∘ (id ⊗₁ (f ⊗₁ g))) ∘ α⇒            ≈˘⟨ eval-comm ⟩∘⟨refl ⟩
    uncurry [ f ⊗₁ g , h ]₁ ∘ α⇒                         ≈˘⟨ uncurry²-curry₂-∘ ⟩
    uncurry (uncurry (curry₂ ∘ [ f ⊗₁ g , h ]₁))             ∎)

-- Iterated currying sends a name to the name of the curried map.
abstract
  curry₂-⌜⌝ : {g : A ⊗₀ B ⇒ C} → curry₂ ∘ ⌜ g ⌝ ≈ ⌜ curry g ⌝
  curry₂-⌜⌝ {g = g} = uncurry²-injective (begin
    uncurry (uncurry (curry₂ ∘ ⌜ g ⌝))                ≈⟨ uncurry-resp-≈ uncurry-∘ ⟩
    uncurry (uncurry curry₂ ∘ (⌜ g ⌝ ⊗₁ id))          ≈⟨ uncurry-∘ ⟩
    uncurry (uncurry curry₂) ∘ ((⌜ g ⌝ ⊗₁ id) ⊗₁ id)  ≈⟨ uncurry²-curry₂ ⟩∘⟨refl ⟩
    (eval ∘ α⇒) ∘ ((⌜ g ⌝ ⊗₁ id) ⊗₁ id)              ≈⟨ extendˡ α⇒-⊗id-commute ⟩
    (eval ∘ (⌜ g ⌝ ⊗₁ id)) ∘ α⇒                      ≈⟨ eval-⌜⌝ ⟩∘⟨refl ⟩
    (g ∘ λ⇒) ∘ α⇒                                    ≈⟨ pullʳ coherence₁ ⟩
    g ∘ (λ⇒ ⊗₁ id)                                   ≈˘⟨ eval-curry ⟩∘⟨refl ⟩
    uncurry (curry g) ∘ (λ⇒ ⊗₁ id)                   ≈˘⟨ uncurry-∘ ⟩
    uncurry (curry g ∘ λ⇒)                           ≈˘⟨ uncurry-resp-≈ eval-⌜⌝ ⟩
    uncurry (uncurry ⌜ curry g ⌝)                    ∎)
