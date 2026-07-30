{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

-- Opposites of enriched natural transformations and natural isomorphisms.

module Categories.Enriched.NaturalTransformation.Opposite
  {o ℓ e} {V : Category o ℓ e} {M : Monoidal V} (S : Symmetric M) where

import Categories.Enriched.Category as Enriched

open Category V
open Monoidal M
open Symmetric S using (braided)
open import Categories.Category.Monoidal.Braided.Properties braided
  using () renaming (module Shorthands to BraidShorthands)
open import Categories.Category.Monoidal.Properties M using (coherence-inv₃)
open import Categories.Category.Monoidal.Reasoning M
open import Categories.Category.Monoidal.Symmetric.Properties S
  using (unitˡ-braiding; unitʳ-braiding)
open import Categories.Category.Monoidal.Utilities M using (module Shorthands)
open import Categories.Enriched.Category.Opposite S renaming (op to opE)
open import Categories.Enriched.Functor M using (Functor)
open import Categories.Enriched.Functor.Opposite S using (opF)
open import Categories.Enriched.NaturalTransformation M
  using (NaturalTransformation; NTHelper; ntHelper)
open import Categories.Enriched.NaturalTransformation.NaturalIsomorphism M
  using (NaturalIsomorphism; niHelper; _ᵢ[_])
open import Categories.Morphism as Morphism using (Iso)
open import Categories.Morphism.Reasoning V
open BraidShorthands
open Shorthands
open NaturalTransformation

module _ {c d} {C : Enriched.Category M c} {D : Enriched.Category M d} where
  private
    module C = Enriched.Category C
    module D = Enriched.Category D

  private
    op-∘ : {A B C : D.Obj} {f : unit ⇒ D.hom B A} {g : unit ⇒ D.hom C B} →
      (D.⊚ ∘ σ⇒) ∘ (g ⊗₁ f) ∘ λ⇐ ≈ D.⊚ ∘ (f ⊗₁ g) ∘ λ⇐
    op-∘ {f = f} {g} = begin
      (D.⊚ ∘ σ⇒) ∘ (g ⊗₁ f) ∘ λ⇐  ≈⟨ pullʳ (pullˡ σ⇒-comm) ⟩
      D.⊚ ∘ (((f ⊗₁ g) ∘ σ⇒) ∘ λ⇐)  ≈⟨ refl⟩∘⟨ pullʳ unitˡ-braiding ⟩
      D.⊚ ∘ (f ⊗₁ g) ∘ ρ⇐         ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ coherence-inv₃ ⟩
      D.⊚ ∘ (f ⊗₁ g) ∘ λ⇐         ∎

    opHelper : {F G : Functor C D} → NaturalTransformation G F →
      NTHelper (opF F) (opF G)
    opHelper {F} {G} α = record
      { comp = NaturalTransformation.comp α
      ; commute = λ { {X} {Y} → begin
          (D.⊚ ∘ σ⇒) ∘ (α [ Y ] ⊗₁ F.₁) ∘ λ⇐   ≈⟨ pullʳ (pullˡ σ⇒-comm) ⟩
          D.⊚ ∘ ((F.₁ ⊗₁ α [ Y ]) ∘ σ⇒) ∘ λ⇐   ≈⟨ refl⟩∘⟨ pullʳ unitˡ-braiding ⟩
          D.⊚ ∘ (F.₁ ⊗₁ α [ Y ]) ∘ ρ⇐          ≈˘⟨ α.commute ⟩
          D.⊚ ∘ (α [ X ] ⊗₁ G.₁) ∘ λ⇐          ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ unitʳ-braiding ⟩
          D.⊚ ∘ (α [ X ] ⊗₁ G.₁) ∘ σ⇒ ∘ ρ⇐     ≈⟨ refl⟩∘⟨ pullˡ (⟺ σ⇒-comm) ⟩
          D.⊚ ∘ (σ⇒ ∘ (G.₁ ⊗₁ α [ X ])) ∘ ρ⇐   ≈⟨ assoc²δγ ⟩
          (D.⊚ ∘ σ⇒) ∘ (G.₁ ⊗₁ α [ X ]) ∘ ρ⇐   ∎ }
      }
      where
      module F = Functor F
      module G = Functor G
      module α = NaturalTransformation α

  opNT : {F G : Functor C D} → NaturalTransformation G F →
    NaturalTransformation (opF F) (opF G)
  opNT α = ntHelper (opHelper α)

  opNI : {F G : Functor C D} → NaturalIsomorphism F G →
    NaturalIsomorphism (opF F) (opF G)
  opNI α = niHelper record
    { F⇒G = opHelper (Morphism._≅_.to α)
    ; F⇐G = opHelper (Morphism._≅_.from α)
    ; iso = λ X → record
      { isoˡ = op-∘ ○ Morphism.Iso.isoˡ (Morphism._≅_.iso (α ᵢ[ X ]))
      ; isoʳ = op-∘ ○ Morphism.Iso.isoʳ (Morphism._≅_.iso (α ᵢ[ X ]))
      }
    }
