{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category; module Definitions)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Monoidal.Interchange using (HasInterchange)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

-- The canonical hom functor of an enriched category into the self-enrichment
-- of its symmetric monoidal closed base.

module Categories.Category.Monoidal.Closed.SelfEnrichment
  {o ℓ e} {𝒱 : Category o ℓ e} {M : Monoidal 𝒱}
  (S : Symmetric M) (Cl : Closed M) where

open import Data.Product using (_,_)

import Categories.Enriched.Category as Enriched
import Categories.Enriched.Category.Opposite as EnrichedOpposite
import Categories.Category.Construction.Core 𝒱 as Core

open Category 𝒱
open Core.Shorthands using (idᵢ)
open Definitions 𝒱 using (CommutativeSquare)
open Monoidal M
open Closed Cl using ([_,_]₀; [_,_]₁)
open import Categories.Category.Monoidal.Closed.Properties Cl
open import Categories.Category.Monoidal.Closed.Currying Cl using (uncurry²-∘)
open import Categories.Category.Monoidal.Properties M
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Reassociation M using (λ⇒-assoc; λ⇐-assoc)
open import Categories.Category.Monoidal.Utilities M
open import Categories.Enriched.Bifunctor S
  using (BifunctorHelper; bifunctorHelper; appˡ; module FromHelper)
open import Categories.Enriched.Category M using (_[_,_])
open import Categories.Enriched.Functor M using (Functor; Endofunctor)
open import Categories.Enriched.Functor.Opposite S using (opF)
open import Categories.Enriched.NaturalTransformation M using (NaturalTransformation; NTHelper)
open import Categories.Enriched.NaturalTransformation.NaturalIsomorphism M
  using (NaturalIsomorphism; niHelper)
open import Categories.Morphism 𝒱 using (_≅_; Iso)
open import Categories.Morphism.Reasoning 𝒱
open Shorthands
open Symmetric S using (braided; commutative; hexagon₁)
open import Categories.Category.Monoidal.Braided.Properties braided
  using (braiding-coherence-σ′)
open import Categories.Category.Monoidal.Symmetric.Properties S
  using (unitˡ-braiding; unitʳ-braiding) renaming (module Shorthands to BraidShorthands)
open BraidShorthands

open import Categories.Category.Monoidal.Interchange.Braided braided
  using (module swapInner) renaming (hasInterchange to interchange)
open import Categories.Enriched.Category.TensorProduct interchange using (_⊠_)
open HasInterchange interchange
  using ()
  renaming ( natural to interchange-natural
           ; assoc to interchange-assoc
           ; unitˡ to interchange-unitˡ
           )

private
  i⇒ = swapInner.from

-- Enriched profunctors valued in the canonical self-enrichment.
Profunctor : ∀ {a b} → Enriched.Category M a → Enriched.Category M b → Set _
Profunctor 𝒜 ℬ = Functor (EnrichedOpposite.op S 𝒜 ⊠ ℬ) selfEnrichment

SelfEndofunctor : Set _
SelfEndofunctor = Endofunctor selfEnrichment

SelfProfunctor : Set _
SelfProfunctor = Profunctor selfEnrichment selfEnrichment

module SelfNatural {a} {𝒜 : Enriched.Category M a}
  {F G : Functor 𝒜 selfEnrichment} where

  private
    module 𝒜 = Enriched.Category 𝒜
    module F = Functor F
    module G = Functor G

  module FromUnderlying {H I : Functor 𝒜 selfEnrichment} where
    private
      module H = Functor H
      module I = Functor I

    from-underlying : (η : ∀ X → H.₀ X ⇒ I.₀ X) →
      (∀ {X Y} → η Y ∘ uncurry H.₁ ≈ uncurry I.₁ ∘ (id ⊗₁ η X)) →
      NTHelper H I
    from-underlying η natural = record
      { comp = λ X → ⌜ η X ⌝
      ; commute = uncurry-injective (begin
          uncurry (internal-∘ ∘ (⌜ η _ ⌝ ⊗₁ H.₁) ∘ λ⇐)  ≈⟨ uncurry-∘-⌜⌝ˡ ⟩
          η _ ∘ uncurry H.₁                             ≈⟨ natural ⟩
          uncurry I.₁ ∘ (id ⊗₁ η _)                     ≈˘⟨ uncurry-∘-⌜⌝ʳ ⟩
          uncurry (internal-∘ ∘ (I.₁ ⊗₁ ⌜ η _ ⌝) ∘ ρ⇐)  ∎)
      }

  open FromUnderlying {H = F} {I = G} public
  private module Inverse = FromUnderlying {H = G} {I = F}

  pointwise-iso : (η : ∀ {X} → F.₀ X ≅ G.₀ X) →
    (∀ {X Y} → _≅_.from (η {Y}) ∘ uncurry F.₁
      ≈ uncurry G.₁ ∘ (id ⊗₁ _≅_.from (η {X}))) →
    NaturalIsomorphism F G
  pointwise-iso η natural =
    niHelper record
      { F⇒G = from-underlying (λ X → _≅_.from (η {X})) natural
      ; F⇐G = Inverse.from-underlying (λ X → _≅_.to (η {X}))
          (conjugate-from (idᵢ ⊗ᵢ η) η (⟺ natural))
      ; iso = λ X → record
        { isoˡ = ⌜∘⌝ ○ ⌜⌝-resp-≈ (Iso.isoˡ (_≅_.iso (η {X})))
        ; isoʳ = ⌜∘⌝ ○ ⌜⌝-resp-≈ (Iso.isoʳ (_≅_.iso (η {X})))
        }
      }

module SelfNaturalᵒ {a} {𝒜 : Enriched.Category M a}
  {F G : Functor 𝒜 (EnrichedOpposite.op S selfEnrichment)} where

  private
    module F = Functor F
    module G = Functor G

    variable
      A B C : Obj -- closed arguments
      W : Obj -- source role

    uncurry-⊚ᵒʳ : {f : W ⇒ [ B , C ]₀} {g : A ⇒ B} →
      uncurry ((internal-∘ ∘ σ⇒) ∘ (⌜ g ⌝ ⊗₁ f) ∘ λ⇐) ≈ uncurry f ∘ (id ⊗₁ g)
    uncurry-⊚ᵒʳ {f = f} {g} = uncurry-resp-≈ (begin
      (internal-∘ ∘ σ⇒) ∘ (⌜ g ⌝ ⊗₁ f) ∘ λ⇐    ≈⟨ center σ⇒-comm ⟩
      internal-∘ ∘ (((f ⊗₁ ⌜ g ⌝) ∘ σ⇒) ∘ λ⇐)  ≈⟨ refl⟩∘⟨ pullʳ unitˡ-braiding ⟩
      internal-∘ ∘ (f ⊗₁ ⌜ g ⌝) ∘ ρ⇐           ∎) ○ uncurry-∘-⌜⌝ʳ

    uncurry-⊚ᵒˡ : {f : W ⇒ [ A , B ]₀} {g : B ⇒ C} →
      uncurry ((internal-∘ ∘ σ⇒) ∘ (f ⊗₁ ⌜ g ⌝) ∘ ρ⇐) ≈ g ∘ uncurry f
    uncurry-⊚ᵒˡ {f = f} {g} = uncurry-resp-≈ (begin
      (internal-∘ ∘ σ⇒) ∘ (f ⊗₁ ⌜ g ⌝) ∘ ρ⇐    ≈⟨ center σ⇒-comm ⟩
      internal-∘ ∘ (((⌜ g ⌝ ⊗₁ f) ∘ σ⇒) ∘ ρ⇐)  ≈⟨ refl⟩∘⟨ pullʳ unitʳ-braiding ⟩
      internal-∘ ∘ (⌜ g ⌝ ⊗₁ f) ∘ λ⇐           ∎) ○ uncurry-∘-⌜⌝ˡ

    ⌜∘⌝ᵒ : {f : B ⇒ A} {g : C ⇒ B} →
      (internal-∘ ∘ σ⇒) ∘ (⌜ g ⌝ ⊗₁ ⌜ f ⌝) ∘ λ⇐ ≈ ⌜ f ∘ g ⌝
    ⌜∘⌝ᵒ {f = f} {g} = uncurry-injective (begin
      uncurry ((internal-∘ ∘ σ⇒) ∘ (⌜ g ⌝ ⊗₁ ⌜ f ⌝) ∘ λ⇐)   ≈⟨ uncurry-⊚ᵒʳ ⟩
      uncurry ⌜ f ⌝ ∘ (id ⊗₁ g)                             ≈⟨ eval-⌜⌝ ⟩∘⟨refl ⟩
      (f ∘ λ⇒) ∘ (id ⊗₁ g)                                  ≈⟨ extendˡ unitorˡ-commute-from ⟩
      (f ∘ g) ∘ λ⇒                                          ≈˘⟨ eval-⌜⌝ ⟩
      uncurry ⌜ f ∘ g ⌝                                     ∎)

  module FromUnderlying {H I : Functor 𝒜 (EnrichedOpposite.op S selfEnrichment)} where
    private
      module H = Functor H
      module I = Functor I

    from-underlying : (η : ∀ X → I.₀ X ⇒ H.₀ X) →
      (∀ {X Y} → uncurry H.₁ ∘ (id ⊗₁ η Y) ≈ η X ∘ uncurry I.₁) → NTHelper H I
    from-underlying η natural = record
      { comp = λ X → ⌜ η X ⌝
      ; commute = uncurry-injective (begin
          uncurry ((internal-∘ ∘ σ⇒) ∘ (⌜ η _ ⌝ ⊗₁ H.₁) ∘ λ⇐)   ≈⟨ uncurry-⊚ᵒʳ ⟩
          uncurry H.₁ ∘ (id ⊗₁ η _)                             ≈⟨ natural ⟩
          η _ ∘ uncurry I.₁                                     ≈˘⟨ uncurry-⊚ᵒˡ ⟩
          uncurry ((internal-∘ ∘ σ⇒) ∘ (I.₁ ⊗₁ ⌜ η _ ⌝) ∘ ρ⇐)  ∎)
      }

  open FromUnderlying {H = F} {I = G} public
  private module Inverse = FromUnderlying {H = G} {I = F}

  pointwise-iso : (η : ∀ {X} → F.₀ X ≅ G.₀ X) →
    (∀ {X Y} → uncurry F.₁ ∘ (id ⊗₁ _≅_.to (η {Y}))
      ≈ _≅_.to (η {X}) ∘ uncurry G.₁) → NaturalIsomorphism F G
  pointwise-iso η natural = niHelper record
    { F⇒G = from-underlying (λ X → _≅_.to (η {X})) natural
    ; F⇐G = Inverse.from-underlying (λ X → _≅_.from (η {X}))
        (conjugate-to (idᵢ ⊗ᵢ η) η (⟺ natural))
    ; iso = λ X → record
      { isoˡ = ⌜∘⌝ᵒ ○ ⌜⌝-resp-≈ (Iso.isoˡ (_≅_.iso (η {X})))
      ; isoʳ = ⌜∘⌝ᵒ ○ ⌜⌝-resp-≈ (Iso.isoʳ (_≅_.iso (η {X})))
      }

    }


module Representable {a} (𝒜 : Enriched.Category M a) {X : Enriched.Category.Obj 𝒜} where
  module 𝒜 = Enriched.Category 𝒜

  private variable
    A B C : 𝒜.Obj

  map₁ : 𝒜 [ A , B ] ⇒ [ 𝒜 [ X , A ] , 𝒜 [ X , B ] ]₀
  map₁ = curry 𝒜.⊚

  private abstract
    map₁-id : map₁ {A = A} ∘ 𝒜.id ≈ ⌜id⌝
    map₁-id = uncurry-injective (begin
      uncurry (map₁ ∘ 𝒜.id)         ≈⟨ uncurry-∘ ⟩
      uncurry map₁ ∘ (𝒜.id ⊗₁ id)   ≈⟨ eval-curry ⟩∘⟨refl ⟩
      𝒜.⊚ ∘ (𝒜.id ⊗₁ id)            ≈⟨ 𝒜.unitˡ ⟩
      λ⇒                            ≈˘⟨ eval-⌜id⌝ ⟩
      uncurry ⌜id⌝                  ∎)

    map₁-∘ : map₁ {A = A} {C} ∘ 𝒜.⊚
             ≈ internal-∘ ∘ (map₁ {A = B} {C} ⊗₁ map₁ {A = A} {B})
    map₁-∘ = uncurry-injective (begin
      uncurry (map₁ ∘ 𝒜.⊚)                  ≈⟨ uncurry-∘ ⟩
      uncurry map₁ ∘ (𝒜.⊚ ⊗₁ id)            ≈⟨ eval-curry ⟩∘⟨refl ⟩
      𝒜.⊚ ∘ (𝒜.⊚ ⊗₁ id)                     ≈⟨ 𝒜.⊚-assoc ⟩
      𝒜.⊚ ∘ (id ⊗₁ 𝒜.⊚) ∘ α⇒                ≈˘⟨ eval-curry ⟩
      uncurry (curry _)                     ≈˘⟨ uncurry-resp-≈ internal-∘-curry ⟩
      uncurry (internal-∘ ∘ (map₁ ⊗₁ map₁)) ∎)

  functor : Functor 𝒜 selfEnrichment
  functor = record
    { map₀ = 𝒜 [ X ,_]
    ; map₁ = map₁
    ; identity = map₁-id
    ; homomorphism = map₁-∘
    }

module EnrichedHom {a} (𝒜 : Enriched.Category M a) where
  module 𝒜 = Enriched.Category 𝒜
  open 𝒜 using (⊚; ⊚-assoc)

  private
    variable
      A B C : 𝒜.Obj -- enriched arguments
      W X Y : 𝒜.Obj -- source, comparison, and codomain roles

    𝒜ᵒ 𝒜ᵉ : Enriched.Category M a
    𝒜ᵒ = EnrichedOpposite.op S 𝒜
    𝒜ᵉ = 𝒜ᵒ ⊠ 𝒜

    module op𝒜 = Enriched.Category 𝒜ᵒ
    module Homˡ {X} = Functor (Representable.functor 𝒜 {X = X})
    module Homʳ {B} = Functor (Representable.functor 𝒜ᵒ {X = B})
    module Homˡᵒ {X} = Functor (opF (Representable.functor 𝒜 {X = X}))
    module Homʳᵒ {B} = Functor (opF (Representable.functor 𝒜ᵒ {X = B}))

  homˡ₁ : (X B Y : 𝒜.Obj) → 𝒜 [ B , Y ] ⇒ [ 𝒜 [ X , B ] , 𝒜 [ X , Y ] ]₀
  homˡ₁ X B Y = curry ⊚

  homʳ₁ : (X A B : 𝒜.Obj) → 𝒜 [ X , A ] ⇒ [ 𝒜 [ A , B ] , 𝒜 [ X , B ] ]₀
  homʳ₁ X A B = curry (⊚ ∘ σ⇒)

  private abstract
    whisker-□ : (A B X Y : 𝒜.Obj) → CommutativeSquare
      ((id ⊗₁ ⊚ {A = A} {B = X} {C = Y}) ∘ α⇒)
      (σ⇒ ⊗₁ id)
      (⊚ {A = B} {B = A} {C = Y} ∘ σ⇒)
      (⊚ {A = B} {B = X} {C = Y} ∘
        (id ⊗₁ (⊚ {A = B} {B = A} {C = X} ∘ σ⇒)) ∘ α⇒)
    whisker-□ A B X Y = begin
      (⊚ ∘ σ⇒) ∘ (id ⊗₁ ⊚) ∘ α⇒                     ≈⟨ pullʳ (extendʳ σ⇒-comm) ⟩
      ⊚ ∘ (⊚ ⊗₁ id) ∘ σ⇒ ∘ α⇒                       ≈⟨ pullˡ ⊚-assoc ⟩
      (⊚ ∘ (id ⊗₁ ⊚) ∘ α⇒) ∘ σ⇒ ∘ α⇒                ≈⟨ assoc²βε ⟩
      ⊚ ∘ (id ⊗₁ ⊚) ∘ α⇒ ∘ σ⇒ ∘ α⇒                  ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ hexagon₁ ⟩
      ⊚ ∘ (id ⊗₁ ⊚) ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)  ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
      ⊚ ∘ (id ⊗₁ (⊚ ∘ σ⇒)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)        ≈⟨ assoc²εβ ⟩
      (⊚ ∘ (id ⊗₁ (⊚ ∘ σ⇒)) ∘ α⇒) ∘ (σ⇒ ⊗₁ id)      ∎

  abstract
    whisker-comm : (A B X Y : 𝒜.Obj) →
      internal-∘ {X = 𝒜 [ A , X ]}    ∘ (homʳ₁ B A Y ⊗₁ homˡ₁ A X Y)
      ≈ (internal-∘ {Z = 𝒜 [ B , Y ]} ∘ (homˡ₁ B X Y ⊗₁ homʳ₁ B A X)) ∘ σ⇒
    whisker-comm A B X Y = begin
      internal-∘ ∘ (homʳ₁ B A Y ⊗₁ homˡ₁ A X Y)         ≈⟨ internal-∘-curry ⟩
      curry ((⊚ ∘ σ⇒) ∘ (id ⊗₁ ⊚) ∘ α⇒)                 ≈⟨ curry-resp-≈ (whisker-□ A B X Y) ⟩
      curry ((⊚ ∘ (id ⊗₁ (⊚ ∘ σ⇒)) ∘ α⇒) ∘ (σ⇒ ⊗₁ id))  ≈⟨ curry-∘ ⟩
      curry (⊚ ∘ (id ⊗₁ (⊚ ∘ σ⇒)) ∘ α⇒) ∘ σ⇒            ≈˘⟨ internal-∘-curry ⟩∘⟨refl ⟩
      (internal-∘ ∘ (homˡ₁ B X Y ⊗₁ homʳ₁ B A X)) ∘ σ⇒  ∎

    whisker-commᵒ : (A B X Y : 𝒜.Obj) →
      (internal-∘ ∘ σ⇒) ∘ (homʳ₁ A B Y ⊗₁ homˡ₁ A Y X)
      ≈ ((internal-∘ ∘ σ⇒) ∘ (homˡ₁ B Y X ⊗₁ homʳ₁ A B X)) ∘ σ⇒
    whisker-commᵒ A B X Y = begin
      (internal-∘ ∘ σ⇒) ∘ (homʳ₁ A B Y ⊗₁ homˡ₁ A Y X)         ≈⟨ extendˡ σ⇒-comm ⟩
      (internal-∘ ∘ (homˡ₁ A Y X ⊗₁ homʳ₁ A B Y)) ∘ σ⇒         ≈˘⟨ whisker-comm B A Y X ⟩
      internal-∘ ∘ (homʳ₁ A B X ⊗₁ homˡ₁ B Y X)                ≈⟨ introʳ commutative ⟩
      (internal-∘ ∘ (homʳ₁ A B X ⊗₁ homˡ₁ B Y X)) ∘ (σ⇒ ∘ σ⇒)  ≈⟨ assoc²γβ ⟩
      (internal-∘ ∘ ((homʳ₁ A B X ⊗₁ homˡ₁ B Y X) ∘ σ⇒)) ∘ σ⇒  ≈˘⟨ pullʳ σ⇒-comm ⟩∘⟨refl ⟩
      ((internal-∘ ∘ σ⇒) ∘ (homˡ₁ B Y X ⊗₁ homʳ₁ A B X)) ∘ σ⇒  ∎

  homHelper : BifunctorHelper 𝒜ᵒ 𝒜 selfEnrichment
  homHelper = record
    { map₀ = 𝒜 [_,_]
    ; mapˡ = λ A B X → homʳ₁ B A X
    ; mapʳ = homˡ₁
    ; identityˡ = λ A X → Homʳ.identity
    ; identityʳ = λ X A → Homˡ.identity
    ; homomorphismˡ = λ A B C X → Homʳ.homomorphism
    ; homomorphismʳ = λ X A B C → Homˡ.homomorphism
    ; commute = whisker-comm
    }

  homᵒᵖHelper : BifunctorHelper
    (EnrichedOpposite.op S (EnrichedOpposite.op S 𝒜))
    (EnrichedOpposite.op S 𝒜)
    (EnrichedOpposite.op S selfEnrichment)
  homᵒᵖHelper = record
    { map₀ = 𝒜 [_,_]
    ; mapˡ = λ A B X → homʳ₁ A B X
    ; mapʳ = λ A X Y → homˡ₁ A Y X
    ; identityˡ = λ A X → Homʳᵒ.identity
    ; identityʳ = λ A X → Homˡᵒ.identity
    ; homomorphismˡ = λ A B C X → Homʳᵒ.homomorphism
    ; homomorphismʳ = λ A X Y Z → Homˡᵒ.homomorphism
    ; commute = whisker-commᵒ
    }

  homFunctor : Functor 𝒜ᵉ selfEnrichment
  homFunctor = bifunctorHelper homHelper

  homᵒᵖFunctor : Functor
    (EnrichedOpposite.op S (EnrichedOpposite.op S 𝒜) ⊠ EnrichedOpposite.op S 𝒜)
    (EnrichedOpposite.op S selfEnrichment)
  homᵒᵖFunctor = bifunctorHelper homᵒᵖHelper

  homˡFunctor : 𝒜.Obj → Functor 𝒜 selfEnrichment
  homˡFunctor X = Representable.functor 𝒜 {X = X}

  homʳFunctor : 𝒜.Obj → Functor 𝒜ᵒ selfEnrichment
  homʳFunctor B = Representable.functor 𝒜ᵒ {X = B}

  private
    module Hom = Functor homFunctor
    module Homᵒ = Functor homᵒᵖFunctor

  homFunctor-appˡ : Hom.₁ ∘ ((op𝒜.id ⊗₁ id) ∘ λ⇐) ≈ homˡ₁ A B C
  homFunctor-appˡ = FromHelper.diagonal-appˡ homHelper

  homFunctor-appʳ : Hom.₁ ∘ ((id ⊗₁ 𝒜.id) ∘ ρ⇐) ≈ homʳ₁ B A C
  homFunctor-appʳ = FromHelper.diagonal-appʳ homHelper

  homᵒᵖFunctor-appˡ : Homᵒ.₁ ∘ ((op𝒜.id ⊗₁ id) ∘ λ⇐) ≈ homˡ₁ A C B
  homᵒᵖFunctor-appˡ = FromHelper.diagonal-appˡ homᵒᵖHelper

module SelfEnriched = EnrichedHom selfEnrichment
open SelfEnriched using (homˡ₁; homʳ₁)

private module SelfHomᵒ = Functor SelfEnriched.homᵒᵖFunctor

private
  variable
    A B C : Obj -- closed arguments
    W X Y : Obj -- source, parameter, and codomain roles

private abstract
  ⌜post∘⌝ : (X : Obj) {g : A ⇒ B} →
    internal-∘ ∘ (⌜ g ⌝ ⊗₁ id) ∘ λ⇐ ≈ [ id {X} , g ]₁
  ⌜post∘⌝ X {g = g} = uncurry-injective (begin
    uncurry (internal-∘ ∘ (⌜ g ⌝ ⊗₁ id) ∘ λ⇐)
      ≈⟨ uncurry-∘-⌜⌝ˡ ⟩
    g ∘ uncurry id                       ≈⟨ refl⟩∘⟨ elimʳ ⊗.identity ⟩
    g ∘ eval                             ≈˘⟨ eval-comm-cod ⟩
    uncurry [ id , g ]₁                  ∎)

  ⌜pre∘⌝ : (B : Obj) {f : X ⇒ A} →
    internal-∘ ∘ (id ⊗₁ ⌜ f ⌝) ∘ ρ⇐ ≈ [ f , id {B} ]₁
  ⌜pre∘⌝ B {f = f} = uncurry-injective (begin
    uncurry (internal-∘ ∘ (id ⊗₁ ⌜ f ⌝) ∘ ρ⇐)
      ≈⟨ uncurry-∘-⌜⌝ʳ ⟩
    uncurry id ∘ (id ⊗₁ f)                 ≈⟨ elimʳ ⊗.identity ⟩∘⟨refl ⟩
    eval ∘ (id ⊗₁ f)                       ≈˘⟨ eval-comm-dom ⟩
    uncurry [ f , id ]₁                    ∎)

abstract
  ⌜homˡ⌝ : {g : A ⇒ B} → homˡ₁ X A B ∘ ⌜ g ⌝ ≈ ⌜ [ id , g ]₁ ⌝
  ⌜homˡ⌝ {X = X} {g = g} = uncurry-injective (begin
    uncurry (homˡ₁ _ _ _ ∘ ⌜ g ⌝)                 ≈⟨ uncurry-∘ ⟩
    uncurry (homˡ₁ _ _ _) ∘ (⌜ g ⌝ ⊗₁ id)         ≈⟨ eval-curry ⟩∘⟨refl ⟩
    internal-∘ ∘ (⌜ g ⌝ ⊗₁ id)                    ≈⟨ introʳ unitorˡ.isoˡ ⟩
    (internal-∘ ∘ (⌜ g ⌝ ⊗₁ id)) ∘ (λ⇐ ∘ λ⇒)      ≈⟨ pullˡ assoc ⟩
    (internal-∘ ∘ ((⌜ g ⌝ ⊗₁ id) ∘ λ⇐)) ∘ λ⇒      ≈⟨ ⌜post∘⌝ X ⟩∘⟨refl ⟩
    [ id , g ]₁ ∘ λ⇒                              ≈˘⟨ eval-⌜⌝ ⟩
    uncurry ⌜ [ id , g ]₁ ⌝                       ∎)

  ⌜homʳ⌝ : {f : X ⇒ A} → homʳ₁ X A B ∘ ⌜ f ⌝ ≈ ⌜ [ f , id ]₁ ⌝
  ⌜homʳ⌝ {B = B} {f = f} = uncurry-injective (begin
    uncurry (homʳ₁ _ _ _ ∘ ⌜ f ⌝)                 ≈⟨ uncurry-∘ ⟩
    uncurry (homʳ₁ _ _ _) ∘ (⌜ f ⌝ ⊗₁ id)         ≈⟨ eval-curry ⟩∘⟨refl ⟩
    (internal-∘ ∘ σ⇒) ∘ (⌜ f ⌝ ⊗₁ id)             ≈⟨ pullʳ σ⇒-comm ⟩
    internal-∘ ∘ (id ⊗₁ ⌜ f ⌝) ∘ σ⇒               ≈⟨ refl⟩∘⟨ refl⟩∘⟨ braiding-coherence-σ′ ⟩
    internal-∘ ∘ (id ⊗₁ ⌜ f ⌝) ∘ ρ⇐ ∘ λ⇒          ≈⟨ assoc²εβ ⟩
    (internal-∘ ∘ (id ⊗₁ ⌜ f ⌝) ∘ ρ⇐) ∘ λ⇒        ≈⟨ ⌜pre∘⌝ B ⟩∘⟨refl ⟩
    [ f , id ]₁ ∘ λ⇒                              ≈˘⟨ eval-⌜⌝ ⟩
    uncurry ⌜ [ f , id ]₁ ⌝                       ∎)

  ⌜homᵒᵖ⌝ : (Y : Obj) {g : B ⇒ A} →
    SelfHomᵒ.₁ {X = Y , A} {Y = Y , B} ∘ ((⌜id⌝ ⊗₁ ⌜ g ⌝) ∘ λ⇐)
    ≈ ⌜ [ id , g ]₁ ⌝
  ⌜homᵒᵖ⌝ Y {g = g} = begin
    SelfHomᵒ.₁ ∘ ((⌜id⌝ ⊗₁ ⌜ g ⌝) ∘ λ⇐)               ≈˘⟨ refl⟩∘⟨ (identityʳ ⟩⊗⟨ identityˡ ⟩∘⟨refl) ⟩
    SelfHomᵒ.₁ ∘ (((⌜id⌝ ∘ id) ⊗₁ (id ∘ ⌜ g ⌝)) ∘ λ⇐) ≈⟨ refl⟩∘⟨ (⊗.homomorphism ⟩∘⟨refl) ⟩
    SelfHomᵒ.₁ ∘ (((⌜id⌝ ⊗₁ id) ∘ (id ⊗₁ ⌜ g ⌝)) ∘ λ⇐)
      ≈⟨ refl⟩∘⟨ assoc ⟩
    SelfHomᵒ.₁ ∘ ((⌜id⌝ ⊗₁ id) ∘ ((id ⊗₁ ⌜ g ⌝) ∘ λ⇐))
      ≈⟨ refl⟩∘⟨ (refl⟩∘⟨ ⟺ unitorˡ-commute-to) ⟩
    SelfHomᵒ.₁ ∘ ((⌜id⌝ ⊗₁ id) ∘ (λ⇐ ∘ ⌜ g ⌝))
      ≈⟨ assoc²εβ ⟩
    (SelfHomᵒ.₁ ∘ ((⌜id⌝ ⊗₁ id) ∘ λ⇐)) ∘ ⌜ g ⌝
      ≈⟨ SelfEnriched.homᵒᵖFunctor-appˡ ⟩∘⟨refl ⟩
    homˡ₁ Y _ _ ∘ ⌜ g ⌝                         ≈⟨ ⌜homˡ⌝ ⟩
    ⌜ [ id , g ]₁ ⌝                             ∎

uncurry²-homʳ :
  uncurry (uncurry (homʳ₁ A B C))
  ≈ (eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ (σ⇒ ⊗₁ id)
uncurry²-homʳ {A} {B} {C} = begin
  uncurry (uncurry (homʳ₁ A B C))           ≈⟨ uncurry-resp-≈ eval-curry ⟩
  uncurry (internal-∘ ∘ σ⇒)                 ≈⟨ uncurry-∘ ⟩
  uncurry internal-∘ ∘ (σ⇒ ⊗₁ id)           ≈⟨ eval-internal-∘ ⟩∘⟨refl ⟩
  (eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ (σ⇒ ⊗₁ id)   ∎

abstract
  evaluate-precomposition : {q : A ⇒ [ Y , X ]₀} {k : W ⇒ [ X , B ]₀} →
    uncurry (uncurry (homʳ₁ Y X B ∘ q)) ∘ ((id ⊗₁ k) ⊗₁ id)
    ≈ uncurry k ∘ (id ⊗₁ uncurry q) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
  evaluate-precomposition {q = q} {k} = begin
    uncurry (uncurry (homʳ₁ _ _ _ ∘ q)) ∘ ((id ⊗₁ k) ⊗₁ id)
      ≈⟨ uncurry²-∘ ⟩∘⟨refl ⟩
    (uncurry (uncurry (homʳ₁ _ _ _)) ∘ ((q ⊗₁ id) ⊗₁ id))
      ∘ ((id ⊗₁ k) ⊗₁ id)
      ≈⟨ pullʳ merge₁ˡ ⟩
    uncurry (uncurry (homʳ₁ _ _ _))
      ∘ (((q ⊗₁ id) ∘ (id ⊗₁ k)) ⊗₁ id)
      ≈⟨ refl⟩∘⟨ merge₂ʳ ⟩⊗⟨refl ⟩
    uncurry (uncurry (homʳ₁ _ _ _)) ∘ ((q ⊗₁ (id ∘ k)) ⊗₁ id)
      ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ identityˡ) ⟩⊗⟨refl ⟩
    uncurry (uncurry (homʳ₁ _ _ _)) ∘ ((q ⊗₁ k) ⊗₁ id)
      ≈⟨ uncurry²-homʳ ⟩∘⟨refl ⟩
    ((eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ (σ⇒ ⊗₁ id)) ∘ ((q ⊗₁ k) ⊗₁ id)
      ≈⟨ pullʳ (parallel σ⇒-comm id-comm-sym) ⟩
    (eval ∘ (id ⊗₁ eval) ∘ α⇒) ∘ (((k ⊗₁ q) ⊗₁ id) ∘ (σ⇒ ⊗₁ id))
      ≈⟨ assoc²βε ⟩
    eval ∘ (id ⊗₁ eval) ∘ α⇒ ∘ ((k ⊗₁ q) ⊗₁ id) ∘ (σ⇒ ⊗₁ id)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assoc-commute-from ⟩
    eval ∘ (id ⊗₁ eval) ∘ (k ⊗₁ (q ⊗₁ id)) ∘ α⇒ ∘ (σ⇒ ⊗₁ id)
      ≈⟨ pull-center (⟺ ⊗-distrib-over-∘) ⟩
    eval ∘ (((id ∘ k) ⊗₁ (eval ∘ (q ⊗₁ id))) ∘ α⇒ ∘ (σ⇒ ⊗₁ id))
      ≈⟨ pushʳ (identityˡ ⟩⊗⟨refl ⟩∘⟨refl) ⟩
    (eval ∘ (k ⊗₁ uncurry q)) ∘ (α⇒ ∘ (σ⇒ ⊗₁ id))
      ≈⟨ (refl⟩∘⟨ serialize₁₂) ⟩∘⟨refl ⟩
    (eval ∘ (k ⊗₁ id) ∘ (id ⊗₁ uncurry q)) ∘ (α⇒ ∘ (σ⇒ ⊗₁ id))
      ≈⟨ assoc²βγ ⟩
    uncurry k ∘ (id ⊗₁ uncurry q) ∘ α⇒ ∘ (σ⇒ ⊗₁ id) ∎
