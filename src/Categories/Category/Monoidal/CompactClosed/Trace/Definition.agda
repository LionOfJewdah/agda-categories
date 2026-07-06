{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)
open import Categories.Category.Monoidal.Rigid using (LeftRigid)
open import Data.Product using (_,_)

module Categories.Category.Monoidal.CompactClosed.Trace.Definition
    {o ℓ e} {C : Category o ℓ e}
    (M : Monoidal C)
    (S : Symmetric M)
    (R : LeftRigid M) where

open Category C
open Monoidal M
open LeftRigid R using (_⁻¹; η; ε; dual₁)

open import Categories.Category.Monoidal.Reasoning M
open TensorIdentity using (id⊗id; whisker-∘)
open import Categories.Morphism.Reasoning C
open import Categories.Category.Monoidal.Braided.Properties (Symmetric.braided S)
  using () renaming (module Shorthands to BraidShorthands)
open import Categories.Category.Monoidal.Rigid.Dual M R
  using (dual₁-cup; dual₁-cap)
import Categories.Category.Monoidal.Utilities M as MonUtil
open MonUtil.Shorthands
open BraidShorthands using (σ⇒; σ-commute)

private
  commute₂₁ : ∀ {A B P Q} {f : A ⇒ B} {g : P ⇒ Q} →
    (id {B} ⊗₁ g) ∘ (f ⊗₁ id {P}) ≈ (f ⊗₁ id {Q}) ∘ (id {A} ⊗₁ g)
  commute₂₁ {f = f} {g} = begin
    (id ⊗₁ g) ∘ (f ⊗₁ id)  ≈˘⟨ serialize₂₁ {f = f} {g = g} ⟩
    f ⊗₁ g                 ≈⟨ serialize₁₂ {f = f} {g = g} ⟩
    (f ⊗₁ id) ∘ (id ⊗₁ g)  ∎

  commute₁₂ : ∀ {A B P Q} {f : A ⇒ B} {g : P ⇒ Q} →
    (f ⊗₁ id {Q}) ∘ (id {A} ⊗₁ g) ≈ (id {B} ⊗₁ g) ∘ (f ⊗₁ id {P})
  commute₁₂ = ⟺ commute₂₁

capᵀ : ∀ {B X} → (B ⊗₀ X) ⊗₀ X ⁻¹ ⇒ B
capᵀ {B} {X}   = ρ⇒ ∘ (id ⊗₁ ε {X}) ∘ (id ⊗₁ σ⇒ {X} {X ⁻¹}) ∘ α⇒

cupᵀ : ∀ {A X} → A ⇒ (A ⊗₀ X) ⊗₀ X ⁻¹
cupᵀ {A} {X}   = α⇐ ∘ (id ⊗₁ η {X}) ∘ ρ⇐

whiskerʳ : ∀ {A B X} → A ⊗₀ X ⇒ B ⊗₀ X → (A ⊗₀ X) ⊗₀ X ⁻¹ ⇒ (B ⊗₀ X) ⊗₀ X ⁻¹
whiskerʳ {X = X} f = f ⊗₁ id {X ⁻¹}

trace-expanded : ∀ {A B X} → A ⊗₀ X ⇒ B ⊗₀ X → A ⇒ B
trace-expanded {A} {B} {X} f =
  ρ⇒ ∘ (id ⊗₁  ε)
     ∘ (id ⊗₁ σ⇒) ∘ α⇒
     ∘ (f  ⊗₁ id) ∘ α⇐
     ∘ (id ⊗₁  η) ∘ ρ⇐

trace : ∀ {A B X} → A ⊗₀ X ⇒ B ⊗₀ X → A ⇒ B
trace f = capᵀ ∘ whiskerʳ f ∘ cupᵀ

trace-resp-≈ : ∀ {A B X} {f g : A ⊗₀ X ⇒ B ⊗₀ X} → f ≈ g → trace f ≈ trace g
trace-resp-≈ f≈g = refl⟩∘⟨ ((f≈g ⟩⊗⟨refl) ⟩∘⟨refl)

trace-expand : ∀ {A B X} {f : A ⊗₀ X ⇒ B ⊗₀ X} → trace f ≈ trace-expanded f
trace-expand {A} {B} {X} {f} = begin
  trace f
    ≈⟨ assoc ⟩
  ρ⇒ {B} ∘ (((id {B} ⊗₁ ε {X}) ∘ ((id {B} ⊗₁ σ⇒ {X} {X ⁻¹}) ∘ α⇒ {B} {X} {X ⁻¹}))
    ∘ ((f ⊗₁ id {X ⁻¹}) ∘ cupᵀ {A} {X}))
    ≈⟨ refl⟩∘⟨ assoc ⟩
  ρ⇒ {B} ∘ ((id {B} ⊗₁ ε {X})
    ∘ (((id {B} ⊗₁ σ⇒ {X} {X ⁻¹}) ∘ α⇒ {B} {X} {X ⁻¹})
    ∘ ((f ⊗₁ id {X ⁻¹}) ∘ cupᵀ {A} {X})))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
  ρ⇒ {B} ∘ (id {B} ⊗₁ ε {X})
    ∘ (id {B} ⊗₁ σ⇒ {X} {X ⁻¹}) ∘ α⇒ {B} {X} {X ⁻¹}
    ∘ (f ⊗₁ id {X ⁻¹}) ∘ α⇐ {A} {X} {X ⁻¹}
    ∘ (id {A} ⊗₁ η {X}) ∘ ρ⇐ {A}
    ∎

trace-whiskerˡ-expand : ∀ {X Y A B} {f : A ⊗₀ X ⇒ B ⊗₀ X} →
  id {Y} ⊗₁ trace {X = X} f
  ≈ (id {Y} ⊗₁ ρ⇒)
    ∘ (id {Y} ⊗₁ (id ⊗₁ ε))
    ∘ (id {Y} ⊗₁ (id ⊗₁ σ⇒))
    ∘ (id {Y} ⊗₁ α⇒)
    ∘ (id {Y} ⊗₁ (f ⊗₁ id))
    ∘ (id {Y} ⊗₁ α⇐)
    ∘ (id {Y} ⊗₁ (id ⊗₁ η))
    ∘ (id {Y} ⊗₁ ρ⇐)
trace-whiskerˡ-expand {X} {Y} {A} {B} {f} = begin
  id {Y} ⊗₁ trace {X = X} f
    ≈⟨ refl⟩⊗⟨ trace-expand {f = f} ⟩
  id {Y} ⊗₁ trace-expanded f
    ≈⟨ whisker-∘ ⟩
  (id {Y} ⊗₁ ρ⇒) ∘ (id {Y} ⊗₁ ((id ⊗₁ ε) ∘ (id ⊗₁ σ⇒) ∘ α⇒ ∘ (f ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ η) ∘ ρ⇐))
    ≈⟨ refl⟩∘⟨ whisker-∘ ⟩
  (id {Y} ⊗₁ ρ⇒) ∘ (id {Y} ⊗₁ (id ⊗₁ ε)) ∘ (id {Y} ⊗₁ ((id ⊗₁ σ⇒) ∘ α⇒ ∘ (f ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ η) ∘ ρ⇐))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ whisker-∘ ⟩
  (id {Y} ⊗₁ ρ⇒) ∘ (id {Y} ⊗₁ (id ⊗₁ ε)) ∘ (id {Y} ⊗₁ (id ⊗₁ σ⇒)) ∘ (id {Y} ⊗₁ (α⇒ ∘ (f ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ η) ∘ ρ⇐))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ whisker-∘ ⟩
  (id {Y} ⊗₁ ρ⇒) ∘ (id {Y} ⊗₁ (id ⊗₁ ε)) ∘ (id {Y} ⊗₁ (id ⊗₁ σ⇒)) ∘ (id {Y} ⊗₁ α⇒) ∘ (id {Y} ⊗₁ ((f ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ η) ∘ ρ⇐))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ whisker-∘ ⟩
  (id {Y} ⊗₁ ρ⇒) ∘ (id {Y} ⊗₁ (id ⊗₁ ε)) ∘ (id {Y} ⊗₁ (id ⊗₁ σ⇒)) ∘ (id {Y} ⊗₁ α⇒) ∘ (id {Y} ⊗₁ (f ⊗₁ id)) ∘ (id {Y} ⊗₁ (α⇐ ∘ (id ⊗₁ η) ∘ ρ⇐))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ whisker-∘ ⟩
  (id {Y} ⊗₁ ρ⇒) ∘ (id {Y} ⊗₁ (id ⊗₁ ε)) ∘ (id {Y} ⊗₁ (id ⊗₁ σ⇒)) ∘ (id {Y} ⊗₁ α⇒) ∘ (id {Y} ⊗₁ (f ⊗₁ id)) ∘ (id {Y} ⊗₁ α⇐) ∘ (id {Y} ⊗₁ ((id ⊗₁ η) ∘ ρ⇐))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ whisker-∘ ⟩
  (id {Y} ⊗₁ ρ⇒) ∘ (id {Y} ⊗₁ (id ⊗₁ ε)) ∘ (id {Y} ⊗₁ (id ⊗₁ σ⇒)) ∘ (id {Y} ⊗₁ α⇒) ∘ (id {Y} ⊗₁ (f ⊗₁ id)) ∘ (id {Y} ⊗₁ α⇐) ∘ (id {Y} ⊗₁ (id ⊗₁ η)) ∘ (id {Y} ⊗₁ ρ⇐)
    ∎

private
  capᵀ-expand : ∀ {B X W} {h : W ⇒ (B ⊗₀ X) ⊗₀ X ⁻¹} →
    capᵀ {B} {X} ∘ h
    ≈ ρ⇒ ∘ (id {B} ⊗₁ ε {X}) ∘ (id {B} ⊗₁ σ⇒ {X} {X ⁻¹}) ∘ α⇒ ∘ h
  capᵀ-expand {B} {X} {h = h} = begin
    capᵀ {B} {X} ∘ h
      ≈⟨ assoc ⟩
    ρ⇒ {B} ∘ (((id {B} ⊗₁ ε {X}) ∘ ((id {B} ⊗₁ σ⇒ {X} {X ⁻¹}) ∘ α⇒ {B} {X} {X ⁻¹})) ∘ h)
      ≈⟨ refl⟩∘⟨ assoc ⟩
    ρ⇒ {B} ∘ ((id {B} ⊗₁ ε {X}) ∘ (((id {B} ⊗₁ σ⇒ {X} {X ⁻¹}) ∘ α⇒ {B} {X} {X ⁻¹}) ∘ h))
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
    ρ⇒ {B} ∘ (id {B} ⊗₁ ε {X}) ∘ (id {B} ⊗₁ σ⇒ {X} {X ⁻¹}) ∘ α⇒ {B} {X} {X ⁻¹} ∘ h
      ∎

  merge-cup : ∀ {A X Y} {g : X ⇒ Y} →
    (id {A} ⊗₁ (g ⊗₁ id {X ⁻¹})) ∘ (id {A} ⊗₁ η {X})
    ≈ id {A} ⊗₁ ((g ⊗₁ id {X ⁻¹}) ∘ η {X})
  merge-cup {A} {X} {Y} {g} = begin
    (id {A} ⊗₁ (g ⊗₁ id {X ⁻¹})) ∘ (id {A} ⊗₁ η {X})
      ≈˘⟨ ⊗-distrib-over-∘ ⟩
    (id {A} ∘ id {A}) ⊗₁ ((g ⊗₁ id {X ⁻¹}) ∘ η {X})
      ≈⟨ identity² ⟩⊗⟨refl ⟩
    id {A} ⊗₁ ((g ⊗₁ id {X ⁻¹}) ∘ η {X})
      ∎

capᵀ-natural : ∀ {B C X} {f : B ⇒ C} →
  capᵀ {C} {X} ∘ ((f ⊗₁ id {X}) ⊗₁ id {X ⁻¹})
  ≈ f ∘ capᵀ {B} {X}
capᵀ-natural {B} {C} {X} {f} =
  let
    ρC = ρ⇒ {C}
    ρB = ρ⇒ {B}
    eC = id {C} ⊗₁ ε {X}
    eB = id {B} ⊗₁ ε {X}
    sC = id {C} ⊗₁ σ⇒ {X} {X ⁻¹}
    sB = id {B} ⊗₁ σ⇒ {X} {X ⁻¹}
    αC = α⇒ {C} {X} {X ⁻¹}
    αB = α⇒ {B} {X} {X ⁻¹}
    ff = (f ⊗₁ id {X}) ⊗₁ id {X ⁻¹}
    fXX = f ⊗₁ id {X ⊗₀ X ⁻¹}
    fXX′ = f ⊗₁ id {X ⁻¹ ⊗₀ X}
    fU = f ⊗₁ id {unit}
    id⊗₁id⁻¹ = id {X} ⊗₁ id {X ⁻¹}
    fXX-id : (f ⊗₁ id⊗₁id⁻¹) ∘ αB ≈ fXX ∘ αB
    fXX-id = (refl⟩⊗⟨ id⊗id) ⟩∘⟨refl
  in begin
  capᵀ {C} {X} ∘ ff
    ≈⟨ capᵀ-expand {h = ff} ⟩
  ρC ∘ eC ∘ sC ∘ (αC ∘ ff)                    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-commute-from ⟩
  ρC ∘ eC ∘ sC ∘ ((f ⊗₁ id⊗₁id⁻¹) ∘ αB)       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ fXX-id ⟩
  ρC ∘ eC ∘ sC ∘ (fXX ∘ αB)                   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ sym-assoc ⟩
  ρC ∘ eC ∘ (sC ∘ fXX) ∘ αB                   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (commute₂₁ ⟩∘⟨refl) ⟩
  ρC ∘ eC ∘ (fXX′ ∘ sB) ∘ αB                  ≈⟨ refl⟩∘⟨ refl⟩∘⟨ assoc ⟩
  ρC ∘ eC ∘ fXX′ ∘ (sB ∘ αB)                  ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  ρC ∘ (eC ∘ fXX′) ∘ (sB ∘ αB)                ≈⟨ refl⟩∘⟨ (commute₂₁ ⟩∘⟨refl) ⟩
  ρC ∘ (fU ∘ eB) ∘ (sB ∘ αB)                  ≈⟨ refl⟩∘⟨ assoc ⟩
  ρC ∘ fU ∘ (eB ∘ (sB ∘ αB))                  ≈⟨ sym-assoc ⟩
  (ρC ∘ fU) ∘ (eB ∘ (sB ∘ αB))                ≈⟨ unitorʳ-commute-from ⟩∘⟨refl ⟩
  (f ∘ ρB) ∘ (eB ∘ (sB ∘ αB))                 ≈⟨ assoc ⟩
  f ∘ capᵀ {B} {X}                            ∎

cupᵀ-natural : ∀ {A B X} {f : A ⇒ B} →
  ((f ⊗₁ id {X}) ⊗₁ id {X ⁻¹}) ∘ cupᵀ {A} {X}
  ≈ cupᵀ {B} {X} ∘ f
cupᵀ-natural {A} {B} {X} {f} =
  let
    αA = α⇐ {A} {X} {X ⁻¹}
    αB = α⇐ {B} {X} {X ⁻¹}
    cupA = id {A} ⊗₁ η {X}
    cupB = id {B} ⊗₁ η {X}
    ρA = ρ⇐ {A}
    ρB = ρ⇐ {B}
    ff = (f ⊗₁ id {X}) ⊗₁ id {X ⁻¹}
    fXX′ = f ⊗₁ (id {X} ⊗₁ id {X ⁻¹})
    fXX = f ⊗₁ id {X ⊗₀ X ⁻¹}
    fU = f ⊗₁ id {unit}
    fXX-id : fXX′ ≈ fXX
    fXX-id = refl⟩⊗⟨ id⊗id
    α-fXX-id : αB ∘ (fXX′ ∘ (cupA ∘ ρA)) ≈ αB ∘ (fXX ∘ (cupA ∘ ρA))
    α-fXX-id = refl⟩∘⟨ (fXX-id ⟩∘⟨refl)
  in begin
  ff ∘ cupᵀ {A} {X}            ≈⟨ sym-assoc ⟩
  (ff ∘ αA) ∘ (cupA ∘ ρA)      ≈⟨ ⟺ assoc-commute-to ⟩∘⟨refl ⟩
  (αB ∘ fXX′) ∘ (cupA ∘ ρA)    ≈⟨ assoc ⟩
  αB ∘ fXX′ ∘ (cupA ∘ ρA)      ≈⟨ α-fXX-id ⟩
  αB ∘ fXX ∘ (cupA ∘ ρA)       ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  αB ∘ (fXX ∘ cupA) ∘ ρA       ≈⟨ refl⟩∘⟨ (commute₁₂ ⟩∘⟨refl) ⟩
  αB ∘ (cupB ∘ fU) ∘ ρA        ≈⟨ refl⟩∘⟨ assoc ⟩
  αB ∘ cupB ∘ (fU ∘ ρA)        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⟺ unitorʳ-commute-to ⟩
  αB ∘ cupB ∘ (ρB ∘ f)         ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  αB ∘ (cupB ∘ ρB) ∘ f         ≈⟨ sym-assoc ⟩
  cupᵀ {B} {X} ∘ f             ∎

cupᵀ-slide : ∀ {X Y A} {g : X ⇒ Y} →
  ((id {A} ⊗₁ g) ⊗₁ id {X ⁻¹}) ∘ cupᵀ {A} {X}
  ≈ (id {A ⊗₀ Y} ⊗₁ dual₁ g) ∘ cupᵀ {A} {Y}
cupᵀ-slide {X} {Y} {A} {g} = begin
  ((id {A} ⊗₁ g) ⊗₁ id {X ⁻¹}) ∘ cupᵀ {A} {X}
    ≈⟨ refl⟩∘⟨ Equiv.refl ⟩
  ((id {A} ⊗₁ g) ⊗₁ id {X ⁻¹})
    ∘ α⇐ {A} {X} {X ⁻¹} ∘ (id {A} ⊗₁ η {X}) ∘ ρ⇐ {A}
    ≈⟨ pullˡ (⟺ (assoc-commute-to {f = id {A}} {g = g} {h = id {X ⁻¹}})) ⟩
  (α⇐ {A} {Y} {X ⁻¹} ∘ (id {A} ⊗₁ (g ⊗₁ id {X ⁻¹})))
    ∘ (id {A} ⊗₁ η {X}) ∘ ρ⇐ {A}
    ≈⟨ assoc ⟩
  α⇐ {A} {Y} {X ⁻¹} ∘ (id {A} ⊗₁ (g ⊗₁ id {X ⁻¹}))
    ∘ (id {A} ⊗₁ η {X}) ∘ ρ⇐ {A}
    ≈⟨ refl⟩∘⟨ pullˡ merge-cup ⟩
  α⇐ {A} {Y} {X ⁻¹} ∘ (id {A} ⊗₁ ((g ⊗₁ id {X ⁻¹}) ∘ η {X})) ∘ ρ⇐ {A}
    ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ ⟺ dual₁-cup) ⟩∘⟨refl ⟩
  α⇐ {A} {Y} {X ⁻¹} ∘ (id {A} ⊗₁ ((id {Y} ⊗₁ dual₁ g) ∘ η {Y})) ∘ ρ⇐ {A}
    ≈⟨ refl⟩∘⟨ split₂ˡ ⟩∘⟨refl ⟩
  α⇐ {A} {Y} {X ⁻¹} ∘ ((id {A} ⊗₁ (id {Y} ⊗₁ dual₁ g)) ∘ (id {A} ⊗₁ η {Y})) ∘ ρ⇐ {A}
    ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇐ {A} {Y} {X ⁻¹} ∘ (id {A} ⊗₁ (id {Y} ⊗₁ dual₁ g))
    ∘ (id {A} ⊗₁ η {Y}) ∘ ρ⇐ {A}
    ≈⟨ sym-assoc ⟩
  (α⇐ {A} {Y} {X ⁻¹} ∘ (id {A} ⊗₁ (id {Y} ⊗₁ dual₁ g)))
    ∘ (id {A} ⊗₁ η {Y}) ∘ ρ⇐ {A}
    ≈⟨ assoc-commute-to {f = id {A}} {g = id {Y}} {h = dual₁ g} ⟩∘⟨refl ⟩
  (((id {A} ⊗₁ id {Y}) ⊗₁ dual₁ g) ∘ α⇐ {A} {Y} {Y ⁻¹})
    ∘ (id {A} ⊗₁ η {Y}) ∘ ρ⇐ {A}
    ≈⟨ (⊗.F-resp-≈ (id⊗id , Equiv.refl) ⟩∘⟨refl) ⟩∘⟨refl ⟩
  ((id {A ⊗₀ Y} ⊗₁ dual₁ g) ∘ α⇐ {A} {Y} {Y ⁻¹})
    ∘ (id {A} ⊗₁ η {Y}) ∘ ρ⇐ {A}
    ≈⟨ assoc ⟩
  (id {A ⊗₀ Y} ⊗₁ dual₁ g) ∘ cupᵀ {A} {Y}
    ∎

private
  capᵀ-slide-mid : ∀ {X Y B} {g : X ⇒ Y} → (B ⊗₀ X) ⊗₀ Y ⁻¹ ⇒ B
  capᵀ-slide-mid {X} {Y} {B} {g} =
    ρ⇒ ∘ (id {B} ⊗₁ ε {Y})
      ∘ (id {B} ⊗₁ (id {Y ⁻¹} ⊗₁ g))
      ∘ (id {B} ⊗₁ σ⇒ {X} {Y ⁻¹})
      ∘ α⇒ {B} {X} {Y ⁻¹}

  capᵀ-slideˡ : ∀ {X Y B} {g : X ⇒ Y} →
    capᵀ {B} {X} ∘ (id {B ⊗₀ X} ⊗₁ dual₁ g)
    ≈ capᵀ-slide-mid {X} {Y} {B} {g}
  capᵀ-slideˡ {X} {Y} {B} {g} = begin
    capᵀ {B} {X} ∘ (id {B ⊗₀ X} ⊗₁ dual₁ g)
      ≈⟨ capᵀ-expand ⟩
    ρ⇒ ∘ (id {B} ⊗₁ ε {X}) ∘ (id {B} ⊗₁ σ⇒ {X} {X ⁻¹})
      ∘ α⇒ {B} {X} {X ⁻¹} ∘ (id {B ⊗₀ X} ⊗₁ dual₁ g)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⊗.F-resp-≈ (⟺ id⊗id , Equiv.refl) ⟩
    ρ⇒ ∘ (id {B} ⊗₁ ε {X}) ∘ (id {B} ⊗₁ σ⇒ {X} {X ⁻¹})
      ∘ α⇒ {B} {X} {X ⁻¹} ∘ ((id {B} ⊗₁ id {X}) ⊗₁ dual₁ g)
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-commute-from {f = id {B}} {g = id {X}} {h = dual₁ g} ⟩
    ρ⇒ ∘ (id {B} ⊗₁ ε {X}) ∘ (id {B} ⊗₁ σ⇒ {X} {X ⁻¹})
      ∘ ((id {B} ⊗₁ (id {X} ⊗₁ dual₁ g)) ∘ α⇒ {B} {X} {Y ⁻¹})
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
    ρ⇒ ∘ (id {B} ⊗₁ ε {X})
      ∘ (id {B} ⊗₁ (σ⇒ {X} {X ⁻¹} ∘ (id {X} ⊗₁ dual₁ g)))
      ∘ α⇒ {B} {X} {Y ⁻¹}
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩⊗⟨ σ-commute {f = id {X}} {g = dual₁ g}) ⟩∘⟨refl ⟩
    ρ⇒ ∘ (id {B} ⊗₁ ε {X})
      ∘ (id {B} ⊗₁ ((dual₁ g ⊗₁ id {X}) ∘ σ⇒ {X} {Y ⁻¹}))
      ∘ α⇒ {B} {X} {Y ⁻¹}
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ whisker-∘ ⟩
    ρ⇒ ∘ (id {B} ⊗₁ ε {X})
      ∘ (id {B} ⊗₁ (dual₁ g ⊗₁ id {X}))
      ∘ (id {B} ⊗₁ σ⇒ {X} {Y ⁻¹}) ∘ α⇒ {B} {X} {Y ⁻¹}
      ≈⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
    ρ⇒ ∘ (id {B} ⊗₁ (ε {X} ∘ (dual₁ g ⊗₁ id {X})))
      ∘ (id {B} ⊗₁ σ⇒ {X} {Y ⁻¹}) ∘ α⇒ {B} {X} {Y ⁻¹}
      ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ dual₁-cap {f = g}) ⟩∘⟨refl ⟩
    ρ⇒ ∘ (id {B} ⊗₁ (ε {Y} ∘ (id {Y ⁻¹} ⊗₁ g)))
      ∘ (id {B} ⊗₁ σ⇒ {X} {Y ⁻¹}) ∘ α⇒ {B} {X} {Y ⁻¹}
      ≈⟨ refl⟩∘⟨ pushˡ whisker-∘ ⟩
    capᵀ-slide-mid {X} {Y} {B} {g}
      ∎

  capᵀ-slideʳ : ∀ {X Y B} {g : X ⇒ Y} →
    capᵀ {B} {Y} ∘ ((id {B} ⊗₁ g) ⊗₁ id {Y ⁻¹})
    ≈ capᵀ-slide-mid {X} {Y} {B} {g}
  capᵀ-slideʳ {X} {Y} {B} {g} = begin
    capᵀ {B} {Y} ∘ ((id {B} ⊗₁ g) ⊗₁ id {Y ⁻¹})
      ≈⟨ capᵀ-expand ⟩
    ρ⇒ ∘ (id {B} ⊗₁ ε {Y}) ∘ (id {B} ⊗₁ σ⇒ {Y} {Y ⁻¹})
      ∘ α⇒ {B} {Y} {Y ⁻¹} ∘ ((id {B} ⊗₁ g) ⊗₁ id {Y ⁻¹})
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ assoc-commute-from {f = id {B}} {g = g} {h = id {Y ⁻¹}} ⟩
    ρ⇒ ∘ (id {B} ⊗₁ ε {Y}) ∘ (id {B} ⊗₁ σ⇒ {Y} {Y ⁻¹})
      ∘ ((id {B} ⊗₁ (g ⊗₁ id {Y ⁻¹})) ∘ α⇒ {B} {X} {Y ⁻¹})
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ merge₂ˡ ⟩
    ρ⇒ ∘ (id {B} ⊗₁ ε {Y})
      ∘ (id {B} ⊗₁ (σ⇒ {Y} {Y ⁻¹} ∘ (g ⊗₁ id {Y ⁻¹})))
      ∘ α⇒ {B} {X} {Y ⁻¹}
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩⊗⟨ σ-commute {f = g} {g = id {Y ⁻¹}}) ⟩∘⟨refl ⟩
    ρ⇒ ∘ (id {B} ⊗₁ ε {Y})
      ∘ (id {B} ⊗₁ ((id {Y ⁻¹} ⊗₁ g) ∘ σ⇒ {X} {Y ⁻¹}))
      ∘ α⇒ {B} {X} {Y ⁻¹}
      ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ whisker-∘ ⟩
    capᵀ-slide-mid {X} {Y} {B} {g}              ∎

capᵀ-slide : ∀ {X Y B} {g : X ⇒ Y} →
  capᵀ {B} {X} ∘ (id {B ⊗₀ X} ⊗₁ dual₁ g) ≈ capᵀ {B} {Y} ∘ ((id {B} ⊗₁ g) ⊗₁ id {Y ⁻¹})
capᵀ-slide {X} {Y} {B} {g} = begin
  capᵀ {B} {X} ∘ (id {B ⊗₀ X} ⊗₁ dual₁ g)    ≈⟨ capᵀ-slideˡ {X} {Y} {B} {g} ⟩
  capᵀ-slide-mid {X} {Y} {B} {g}               ≈˘⟨ capᵀ-slideʳ {X} {Y} {B} {g} ⟩
  capᵀ {B} {Y} ∘ ((id {B} ⊗₁ g) ⊗₁ id {Y ⁻¹}) ∎

trace-slide : ∀ {X Y A B} {f : A ⊗₀ Y ⇒ B ⊗₀ X} {g : X ⇒ Y} →
  trace {X = X} (f ∘ id {A} ⊗₁ g)
  ≈ trace {X = Y} (id {B} ⊗₁ g ∘ f)
trace-slide {X} {Y} {A} {B} {f} {g} =
  let
    fX = f ⊗₁ id {X ⁻¹}
    fY = f ⊗₁ id {Y ⁻¹}
    gx = (id {A} ⊗₁ g) ⊗₁ id {X ⁻¹}
    gy = (id {B} ⊗₁ g) ⊗₁ id {Y ⁻¹}
    dxA = id {A ⊗₀ Y} ⊗₁ dual₁ g
    dxB = id {B ⊗₀ X} ⊗₁ dual₁ g
  in begin
  trace {X = X} (f ∘ id {A} ⊗₁ g)              ≈⟨ refl⟩∘⟨ split₁ʳ ⟩∘⟨refl ⟩
  capᵀ {B} {X} ∘ ((fX ∘ gx) ∘ cupᵀ {A} {X})    ≈⟨ refl⟩∘⟨ assoc ⟩
  capᵀ {B} {X} ∘ (fX ∘ (gx ∘ cupᵀ {A} {X}))    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cupᵀ-slide {A = A} {g = g} ⟩
  capᵀ {B} {X} ∘ (fX ∘ (dxA ∘ cupᵀ {A} {Y}))   ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  capᵀ {B} {X} ∘ ((fX ∘ dxA) ∘ cupᵀ {A} {Y})   ≈⟨ refl⟩∘⟨ (⟺ commute₂₁ ⟩∘⟨refl) ⟩
  capᵀ {B} {X} ∘ ((dxB ∘ fY) ∘ cupᵀ {A} {Y})   ≈⟨ ⟺ assoc²γδ ⟩
  (capᵀ {B} {X} ∘ dxB) ∘ (fY ∘ cupᵀ {A} {Y})   ≈⟨ capᵀ-slide {B = B} {g = g} ⟩∘⟨refl ⟩
  (capᵀ {B} {Y} ∘ gy) ∘ (fY ∘ cupᵀ {A} {Y})    ≈⟨ assoc ⟩
  capᵀ {B} {Y} ∘ (gy ∘ (fY ∘ cupᵀ {A} {Y}))    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  capᵀ {B} {Y} ∘ ((gy ∘ fY) ∘ cupᵀ {A} {Y})    ≈⟨ refl⟩∘⟨ (merge₁ʳ ⟩∘⟨refl) ⟩
  trace {X = Y} (id {B} ⊗₁ g ∘ f)              ∎

trace-tightenₗ : ∀ {X A B C} {f : B ⇒ C} {g : A ⊗₀ X ⇒ B ⊗₀ X} →
  trace {X = X} (f ⊗₁ id {X} ∘ g) ≈ f ∘ trace {X = X} g
trace-tightenₗ {X} {A} {B} {C} {f} {g} =
  let
    ff = (f ⊗₁ id {X}) ⊗₁ id {X ⁻¹}
    gg = g ⊗₁ id {X ⁻¹}
  in begin
  trace {X = X} (f ⊗₁ id {X} ∘ g)
    ≈⟨ refl⟩∘⟨ (split₁ʳ {f = f ⊗₁ id {X}} {g = g} {h = id {X ⁻¹}} ⟩∘⟨refl) ⟩
  capᵀ {C} {X} ∘ ((ff ∘ gg) ∘ cupᵀ {A} {X})
    ≈⟨ refl⟩∘⟨ assoc ⟩
  capᵀ {C} {X} ∘ (ff ∘ (gg ∘ cupᵀ {A} {X}))
    ≈⟨ sym-assoc ⟩
  (capᵀ {C} {X} ∘ ff) ∘ (gg ∘ cupᵀ {A} {X})
    ≈⟨ capᵀ-natural {B = B} {C = C} {X = X} {f = f} ⟩∘⟨refl ⟩
  (f ∘ capᵀ {B} {X}) ∘ (gg ∘ cupᵀ {A} {X})
    ≈⟨ assoc ⟩
  f ∘ (capᵀ {B} {X} ∘ (gg ∘ cupᵀ {A} {X}))
    ≈⟨ Equiv.refl ⟩
  f ∘ trace {X = X} g
    ∎

trace-tightenᵣ : ∀ {X A B C} {f : B ⊗₀ X ⇒ C ⊗₀ X} {g : A ⇒ B} →
  trace {X = X} (f ∘ g ⊗₁ id {X}) ≈ trace {X = X} f ∘ g
trace-tightenᵣ {X} {A} {B} {C} {f} {g} =
  let
    gg = (g ⊗₁ id {X}) ⊗₁ id {X ⁻¹}
  in begin
  trace {X = X} (f ∘ g ⊗₁ id {X})
    ≈⟨ refl⟩∘⟨ (split₁ˡ {f = f} {g = g ⊗₁ id {X}} {h = id {X ⁻¹}} ⟩∘⟨refl) ⟩
  capᵀ {C} {X} ∘ ((f ⊗₁ id {X ⁻¹} ∘ gg) ∘ cupᵀ {A} {X})
    ≈⟨ refl⟩∘⟨ assoc ⟩
  capᵀ {C} {X} ∘ (f ⊗₁ id {X ⁻¹} ∘ (gg ∘ cupᵀ {A} {X}))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ cupᵀ-natural {A = A} {B = B} {X = X} {f = g} ⟩
  capᵀ {C} {X} ∘ (f ⊗₁ id {X ⁻¹} ∘ (cupᵀ {B} {X} ∘ g))
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  capᵀ {C} {X} ∘ ((f ⊗₁ id {X ⁻¹} ∘ cupᵀ {B} {X}) ∘ g)
    ≈⟨ sym-assoc ⟩
  trace {X = X} f ∘ g
    ∎
