{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Closed using (Closed)
open import Categories.Category.Monoidal.Traced using (Traced)

-- The dualizing object and the ∗-autonomous isomorphism `φ` (Hajgató & Hasegawa,
-- TAC 28(7), 2013, §3).  Given a dualizing `⊥`, this builds the double-dual
-- isomorphism, the natural iso `φ : ([ X , ⊥ ⊗₀ Y ]₀ *) ≅ X ⊗₀ [ Y , unit ]₀`
-- (Lemma 3.2), the compact-closed unit `t` (Corollary 3.4), Lemma 3.5
-- (`t {unit}` is canonical), and the concrete normal form `φ⁻¹ = [ Ψ , id ]₁ ∘ δ⇒`
-- that both Lemma 3.5 and the extranaturality hexagon reduce through.

module Categories.Category.Monoidal.Star-Autonomous.Traced.Duality.Construction
  {o ℓ e} {𝒞 : Category o ℓ e} {M : Monoidal 𝒞}
  (Cl : Closed M) (T : Traced M) where

open import Data.Product using (_,_)
open import Relation.Unary using (Pred)

open import Categories.Category.Monoidal.Symmetric M using (Symmetric)
import Categories.Category.Monoidal.Symmetric.Properties as SymProps

open Category 𝒞
open Monoidal M
open Traced T using (trace; trace⟨_⟩; slide; tightenₗ; tightenᵣ; vanishing₁; superposing; symmetric)
open Symmetric symmetric using (braiding; commutative)
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
open import Categories.Functor using (Functor; _∘F_)
open import Categories.Functor.Properties using ([_]-resp-≅)
open import Categories.Functor.Construction.Constant using (const)
open import Categories.Category.Product using (Product; _※_; πˡ; πʳ)
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism; niHelper; _ⓘᵥ_)
open Shorthands
open BraidShorthands
open SymProps symmetric using (braiding-selfInverse)

open import Categories.Category.Monoidal.Star-Autonomous.Traced.Base Cl T public

private
  variable
    A B C X Y Z : Obj

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
  -- `φ` is natural in `X` and `Y` (Lemma 3.2, second half).  Its source and target
  -- are the functors `G , H : 𝒞 × 𝒞ᵒᵖ → 𝒞` below — covariant in `X`, contravariant
  -- in `Y` — with `φ-≅.from` the components of an isomorphism `G ≃ H`.

  𝒟 : Category o ℓ e
  𝒟 = Product 𝒞 (Category.op 𝒞)

  -- `Pof F` is `(X , Y) ↦ [ [ X , F (X , Y) ]₀ , ⊥ ]₀`: post-compose `[ X ,-]` with the
  -- inner `𝒞ᵒᵖ`-valued functor `F`, then dualize.  Layers 1–3 rewrite the inner `F`.
  Pof : Functor 𝒟 (Category.op 𝒞) → Functor 𝒟 𝒞
  Pof F = [-, ⊥ ] ∘F (Functor.op [-,-] ∘F (πˡ ※ F))

  DD : Functor 𝒞 𝒞           -- double dualization `Z ↦ (Z *) *`
  DD = [-, ⊥ ] ∘F Functor.op [-, ⊥ ]

  -- The inner objects along φ's chain, as `𝒞ᵒᵖ`-valued functors of `(X , Y)`.
  Inner₀ Inner₁ Inner₂ Inner₃ : Functor 𝒟 (Category.op 𝒞)
  Inner₀ = Functor.op ⊗ ∘F (const ⊥ ※ πʳ)                    -- ⊥ ⊗₀ Y
  Inner₁ = Functor.op DD ∘F Inner₀                           -- (⊥ ⊗₀ Y) * *
  Inner₂ = Functor.op [-, ⊥ ] ∘F ([-, [ ⊥ , ⊥ ]₀ ] ∘F πʳ)    -- ([ Y , [ ⊥ , ⊥ ]₀ ]₀) *
  Inner₃ = Functor.op [-, ⊥ ] ∘F ([-, unit ] ∘F πʳ)          -- ([ Y , unit ]₀) *

  -- φ's chain of functors: `G = P₀ ⟶ P₁ ⟶ P₂ ⟶ P₃ ⟶ P₄ ⟶ P₅ = H`.
  G H P₁ P₂ P₃ P₄ : Functor 𝒟 𝒞
  G  = Pof Inner₀
  P₁ = Pof Inner₁
  P₂ = Pof Inner₂
  P₃ = Pof Inner₃
  P₄ = DD ∘F H
  H  = ⊗ ∘F (πˡ ※ ([-, unit ] ∘F πʳ))

  -- `G.F₁ (f , g) = [ [ f , id ⊗₁ g ]₁ , id ]₁` and `H.F₁ (f , g) = f ⊗₁ [ g , id ]₁`,
  -- definitionally.  These pin the naturality square `φ` must satisfy.
  G-F₁-action : {f : X ⇒ A} {g : B ⇒ Y} → Functor.F₁ G (f , g) ≈ [ [ f , id ⊗₁ g ]₁ , id ]₁
  G-F₁-action = Equiv.refl

  H-F₁-action : {f : X ⇒ A} {g : B ⇒ Y} → Functor.F₁ H (f , g) ≈ (f ⊗₁ [ g , id ]₁)
  H-F₁-action = Equiv.refl

  δ⇒ : A ⇒ (A *) *
  δ⇒ = _≅_.from **-≅
  δ⇐ : (A *) * ⇒ A
  δ⇐ = _≅_.to **-≅

  -- Naturality of `δ⁻¹`, the inverse of the double-dual unit, from `δ-natural`.
  **⁻¹-natural : {h : A ⇒ B} → h ∘ δ⇐ ≈ δ⇐ ∘ [ [ h , id ]₁ , id ]₁
  **⁻¹-natural {h = h} = begin
    h ∘ δ⇐                        ≈˘⟨ cancelˡ (_≅_.isoˡ **-≅) ⟩
    δ⇐ ∘ δ⇒ ∘ h ∘ δ⇐              ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    δ⇐ ∘ (δ⇒ ∘ h) ∘ δ⇐            ≈⟨ refl⟩∘⟨ pushˡ (⟺ δ-natural) ⟩
    δ⇐ ∘ [ [ h , id ]₁ , id ]₁ ∘ δ⇒ ∘ δ⇐
                                  ≈⟨ refl⟩∘⟨ elimʳ (_≅_.isoʳ **-≅) ⟩
    δ⇐ ∘ [ [ h , id ]₁ , id ]₁    ∎

  -- φ's two inner maps that carry a variable, read off the p.210 chain.
  -- `v₃` folds `[ ⊥ , ⊥ ]₀ ≅ unit`; `v₂` is the swap-currying.
  v₃ : ([ Y , unit ]₀ *) ⇒ ([ Y , [ ⊥ , ⊥ ]₀ ]₀ *)
  v₃ {Y} = [ [ id , _≅_.from ⊥*-≅ ]₁ , id ]₁

  v₂ : ([ Y , [ ⊥ , ⊥ ]₀ ]₀ *) ⇒ ((⊥ ⊗₀ Y) *) *
  v₂ {Y} = [ _≅_.from (swap-curry-≅ {⊥} {Y} {⊥}) , id ]₁

  -- Their inverses, the layers of `φ⁻¹` (all concrete: `⊥*-≅.to`, `swap-curry-≅.to`).
  v₃⁻¹ : ([ Y , [ ⊥ , ⊥ ]₀ ]₀ *) ⇒ ([ Y , unit ]₀ *)
  v₃⁻¹ {Y} = [ [ id , _≅_.to ⊥*-≅ ]₁ , id ]₁

  v₂⁻¹ : ((⊥ ⊗₀ Y) *) * ⇒ ([ Y , [ ⊥ , ⊥ ]₀ ]₀ *)
  v₂⁻¹ {Y} = [ _≅_.to (swap-curry-≅ {⊥} {Y} {⊥}) , id ]₁

  -- Naturality of each inner map in `Y` (the contravariant variable), one per layer.
  -- `v₃` is the constant `⊥*-≅` on an independent slot, so it just interchanges.
  v₃-natural : {g : B ⇒ Y} → v₃ {Y} ∘ [ [ g , id ]₁ , id ]₁ ≈ [ [ g , id ]₁ , id ]₁ ∘ v₃ {B}
  v₃-natural = dual-push (⟺ hom-interchange)

  -- `v₂` is swap-currying; its naturality is `swap-curry-natural` at `f , h := id`.
  v₂-natural : {g : B ⇒ Y} → v₂ {Y} ∘ [ [ g , id ]₁ , id ]₁ ≈ [ [ id ⊗₁ g , id ]₁ , id ]₁ ∘ v₂ {B}
  v₂-natural {g = g} = dual-push inner
    where
      inner : [ g , id ]₁ ∘ (curry₂ ∘ [ σ⇒ , id ]₁)
            ≈ (curry₂ ∘ [ σ⇒ , id ]₁) ∘ [ id ⊗₁ g , id ]₁
      inner = begin
        [ g , id ]₁ ∘ (curry₂ ∘ [ σ⇒ , id ]₁)
          ≈˘⟨ [-,-].F-resp-≈ (Equiv.refl , [-,-].identity) ⟩∘⟨refl ⟩
        [ g , [ id , id ]₁ ]₁ ∘ (curry₂ ∘ [ σ⇒ , id ]₁)
          ≈⟨ swap-curry-natural {f = id} {g = g} {h = id} ⟩
        (curry₂ ∘ [ σ⇒ , id ]₁) ∘ [ id ⊗₁ g , id ]₁       ∎

  ----------------------------------------------------------------------
  -- Lemma 3.2.  The ∗-autonomous iso `φ`, as the five-step chain of p. 210, packaged as a
  -- `NaturalIsomorphism` over `𝒟 = 𝒞 × 𝒞ᵒᵖ`: the double dual on `⊥ ⊗₀ Y`, swap-currying
  -- `[ ⊥ ⊗₀ Y , ⊥ ]₀ ≅ [ Y , [ ⊥ , ⊥ ]₀ ]₀`, `[ ⊥ , ⊥ ]₀ ≅ unit`, currying back, and the
  -- double dual on `X ⊗₀ [ Y , unit ]₀`.  Each layer is a `NaturalIsomorphism` whose
  -- components are the constituent iso and whose `.commute` is one naturality brick; `φ`
  -- is their vertical composite, so its naturality in `X`, `Y` falls out for free.

  L₁ : NaturalIsomorphism G P₁
  L₁ = niHelper record
    { η       = λ (X , Y) → _≅_.from (dualᵒ (homˡ X (**-≅ {⊥ ⊗₀ Y})))
    ; η⁻¹     = λ (X , Y) → _≅_.to   (dualᵒ (homˡ X (**-≅ {⊥ ⊗₀ Y})))
    ; commute = λ _ → dual-push (homˡ-push (⟺ **⁻¹-natural))
    ; iso     = λ (X , Y) → _≅_.iso  (dualᵒ (homˡ X (**-≅ {⊥ ⊗₀ Y})))
    }

  L₂ : NaturalIsomorphism P₁ P₂
  L₂ = niHelper record
    { η       = λ (X , Y) → _≅_.from (dualᵒ (homˡ X (dualᵒ (swap-curry-≅ {⊥} {Y} {⊥}))))
    ; η⁻¹     = λ (X , Y) → _≅_.to   (dualᵒ (homˡ X (dualᵒ (swap-curry-≅ {⊥} {Y} {⊥}))))
    ; commute = λ _ → dual-push (homˡ-push v₂-natural)
    ; iso     = λ (X , Y) → _≅_.iso  (dualᵒ (homˡ X (dualᵒ (swap-curry-≅ {⊥} {Y} {⊥}))))
    }

  L₃ : NaturalIsomorphism P₂ P₃
  L₃ = niHelper record
    { η       = λ (X , Y) → _≅_.from (dualᵒ (homˡ X (dualᵒ (homˡ Y ⊥*-≅))))
    ; η⁻¹     = λ (X , Y) → _≅_.to   (dualᵒ (homˡ X (dualᵒ (homˡ Y ⊥*-≅))))
    ; commute = λ _ → dual-push (homˡ-push v₃-natural)
    ; iso     = λ (X , Y) → _≅_.iso  (dualᵒ (homˡ X (dualᵒ (homˡ Y ⊥*-≅))))
    }

  L₄ : NaturalIsomorphism P₃ P₄
  L₄ = niHelper record
    { η       = λ (X , Y) → _≅_.from (dualᵒ (≅.sym (curry₂-iso {X} {[ Y , unit ]₀} {⊥})))
    ; η⁻¹     = λ (X , Y) → _≅_.to   (dualᵒ (≅.sym (curry₂-iso {X} {[ Y , unit ]₀} {⊥})))
    ; commute = λ _ → dual-push curry₂-natural
    ; iso     = λ (X , Y) → _≅_.iso  (dualᵒ (≅.sym (curry₂-iso {X} {[ Y , unit ]₀} {⊥})))
    }

  L₅ : NaturalIsomorphism P₄ H
  L₅ = niHelper record
    { η       = λ (X , Y) → _≅_.from (≅.sym (**-≅ {X ⊗₀ [ Y , unit ]₀}))
    ; η⁻¹     = λ (X , Y) → _≅_.to   (≅.sym (**-≅ {X ⊗₀ [ Y , unit ]₀}))
    ; commute = λ _ → ⟺ **⁻¹-natural
    ; iso     = λ (X , Y) → _≅_.iso  (≅.sym (**-≅ {X ⊗₀ [ Y , unit ]₀}))
    }

  -- Lemma 3.2 in full: `φ` is a natural isomorphism `G ≃ H`, the vertical composite of
  -- its five layers.  Its `.commute` is φ's naturality in `X` and `Y`, for free.
  φ-NI : NaturalIsomorphism G H
  φ-NI = L₅ ⓘᵥ L₄ ⓘᵥ L₃ ⓘᵥ L₂ ⓘᵥ L₁

  -- The underlying isomorphism, `φ-≅ : ([ X , ⊥ ⊗₀ Y ]₀ *) ≅ X ⊗₀ [ Y , unit ]₀`.
  φ-≅ : ([ X , ⊥ ⊗₀ Y ]₀ *) ≅ X ⊗₀ [ Y , unit ]₀
  φ-≅ {X} {Y} = record
    { from = NaturalIsomorphism.⇒.η φ-NI (X , Y)
    ; to   = NaturalIsomorphism.⇐.η φ-NI (X , Y)
    ; iso  = NaturalIsomorphism.iso φ-NI (X , Y)
    }

  φ⇒ : (X Y : Obj) → ([ X , ⊥ ⊗₀ Y ]₀ *) ⇒ X ⊗₀ [ Y , unit ]₀
  φ⇒ X Y = _≅_.from (φ-≅ {X} {Y})

  φ⇐′ : (X Y : Obj) → X ⊗₀ [ Y , unit ]₀ ⇒ ([ X , ⊥ ⊗₀ Y ]₀ *)
  φ⇐′ X Y = _≅_.to (φ-≅ {X} {Y})

  -- `φ⁻¹`'s inner reindexing at general `X , Y`: the three covariant `[ Y ,-]`-layers of the
  -- p.210 chain, run backwards, uncurried by `uncurry₂`.  (At `X = Y = unit` this is the `Ψ`
  -- driving `t-unit`.)  `Ψ` reindexes `[ X , ⊥ ⊗₀ Y ]₀` to `[ X ⊗₀ [ Y , unit ]₀ , ⊥ ]₀`.
  Ψ′ : (X Y : Obj) → [ X , ⊥ ⊗₀ Y ]₀ ⇒ [ X ⊗₀ [ Y , unit ]₀ , ⊥ ]₀
  Ψ′ X Y = uncurry₂ ∘ [ id , v₃⁻¹ {Y} ]₁ ∘ [ id , v₂⁻¹ {Y} ]₁ ∘ [ id , δ⇒ {A = ⊥ ⊗₀ Y} ]₁

  -- `φ⁻¹ = [ Ψ , id ]₁ ∘ δ⇒` at general `X , Y`: the four dualized layers of `⇐ φ-NI` (left-nested
  -- as `_ⓘᵥ_` composes them) merge to one hom action by `[-,-]` functoriality (`hom-∘ᵣ`).
  φ⇐-merge′ : (X Y : Obj) → φ⇐′ X Y ≈ [ Ψ′ X Y , id ]₁ ∘ δ⇒ {A = X ⊗₀ [ Y , unit ]₀}
  φ⇐-merge′ X Y = begin
    φ⇐′ X Y
      ≈⟨ (((hom-∘ᵣ ⟩∘⟨refl) ⟩∘⟨refl) ⟩∘⟨refl) ⟩
    (([ [ id , v₂⁻¹ {Y} ]₁ ∘ [ id , δ⇒ {A = ⊥ ⊗₀ Y} ]₁ , id ]₁
        ∘ [ [ id , v₃⁻¹ {Y} ]₁ , id ]₁) ∘ [ uncurry₂ , id ]₁) ∘ δ⇒
      ≈⟨ (hom-∘ᵣ ⟩∘⟨refl) ⟩∘⟨refl ⟩
    ([ [ id , v₃⁻¹ {Y} ]₁ ∘ [ id , v₂⁻¹ {Y} ]₁ ∘ [ id , δ⇒ {A = ⊥ ⊗₀ Y} ]₁ , id ]₁
        ∘ [ uncurry₂ , id ]₁) ∘ δ⇒
      ≈⟨ hom-∘ᵣ ⟩∘⟨refl ⟩
    [ Ψ′ X Y , id ]₁ ∘ δ⇒                                            ∎

  ----------------------------------------------------------------------
  -- Corollary 3.4.  The compact-closed unit `t {X} : unit ⇒ X ⊗₀ X *` is the transpose
  -- `⌜ τ ⌝` (Lemma 3.1, extranatural in `X`) followed by `φ` at the diagonal (natural),
  -- hence extranatural (Lemma 3.3).  Here `X * = [ X , unit ]₀`.

  t : {X : Obj} → unit ⇒ X ⊗₀ [ X , unit ]₀
  t {X} = φ⇒ X X ∘ τ̂ {X} {⊥}

  -- `can`, the canonical `t {unit}` (from `Closed/CompactClosed.agda`).
  can : unit ⇒ unit ⊗₀ [ unit , unit ]₀
  can = (id ⊗₁ ⌜id⌝) ∘ ρ⇐

  φ⇐ : unit ⊗₀ [ unit , unit ]₀ ⇒ ([ unit , ⊥ ⊗₀ unit ]₀ *)
  φ⇐ = _≅_.to (φ-≅ {unit} {unit})

  -- `φ⁻¹`'s four dualized layers (all concrete), left-nested exactly as `_ⓘᵥ_` composes them.
  d₁ d₂ d₃ d₄ : _
  d₁ = [ [ id {unit} , δ⇒ {A = ⊥ ⊗₀ unit} ]₁ , id {⊥} ]₁
  d₂ = [ [ id {unit} , v₂⁻¹ {unit} ]₁ , id {⊥} ]₁
  d₃ = [ [ id {unit} , v₃⁻¹ {unit} ]₁ , id {⊥} ]₁
  d₄ = [ uncurry₂ {unit} {[ unit , unit ]₀} {⊥} , id {⊥} ]₁

  -- Their merged reindexing (contravariant, so the composite reverses), the inner map of `φ⁻¹`.
  Ψ : [ unit , ⊥ ⊗₀ unit ]₀ ⇒ [ unit ⊗₀ [ unit , unit ]₀ , ⊥ ]₀
  Ψ = uncurry₂ ∘ [ id , v₃⁻¹ {unit} ]₁ ∘ [ id , v₂⁻¹ {unit} ]₁ ∘ [ id , δ⇒ {A = ⊥ ⊗₀ unit} ]₁

  -- `φ⁻¹` is `[ Ψ , id ]₁ ∘ δ⇒`: its four dualized layers (definitionally the left-nested
  -- composite above) merge to a single hom action by `[-,-]` functoriality (`hom-∘ᵣ`).
  φ⇐-merge : φ⇐ ≈ [ Ψ , id ]₁ ∘ δ⇒
  φ⇐-merge = begin
    (((d₁ ∘ d₂) ∘ d₃) ∘ d₄) ∘ δ⇒
      ≈⟨ ((hom-∘ᵣ ⟩∘⟨refl) ⟩∘⟨refl) ⟩∘⟨refl ⟩
    (([ [ id , v₂⁻¹ {unit} ]₁ ∘ [ id , δ⇒ {A = ⊥ ⊗₀ unit} ]₁ , id ]₁ ∘ d₃) ∘ d₄) ∘ δ⇒
      ≈⟨ (hom-∘ᵣ ⟩∘⟨refl) ⟩∘⟨refl ⟩
    ([ [ id , v₃⁻¹ {unit} ]₁ ∘ [ id , v₂⁻¹ {unit} ]₁ ∘ [ id , δ⇒ {A = ⊥ ⊗₀ unit} ]₁ , id ]₁ ∘ d₄) ∘ δ⇒
      ≈⟨ hom-∘ᵣ ⟩∘⟨refl ⟩
    [ Ψ , id ]₁ ∘ δ⇒                                                 ∎

  -- `τ` at the unit, right-unitor–shifted: `τ ∘ ρ⇒ ≈ ρ⇒ ∘ eval` (from `τ-unit`).
  τρ : τ {unit} {⊥} ∘ ρ⇒ ≈ ρ⇒ ∘ eval {unit} {⊥ ⊗₀ unit}
  τρ = begin
    τ ∘ ρ⇒                  ≈⟨ τ-unit ⟩∘⟨refl ⟩
    (ρ⇒ ∘ unit-hom⇐) ∘ ρ⇒   ≈⟨ assoc ⟩
    ρ⇒ ∘ unit-hom⇐ ∘ ρ⇒     ≈⟨ refl⟩∘⟨ cancelʳ unitorʳ.isoˡ ⟩
    ρ⇒ ∘ eval               ∎

  -- The double-dual unit at `unit`, folded to `⊥ *`: `⊥*-≅.to = [ i⇒ , id ]₁ ∘ δ⇒`, concretely.
  ⊥to : unit ⇒ [ ⊥ , ⊥ ]₀
  ⊥to = _≅_.to ⊥*-≅

  -- Swap-currying at `⊥ , unit , ⊥`, the layer whose `.to` un-swaps a value of `[ ⊥ , ⊥ ]₀`.
  sc : [ ⊥ ⊗₀ unit , ⊥ ]₀ ≅ [ unit , [ ⊥ , ⊥ ]₀ ]₀
  sc = swap-curry-≅ {⊥} {unit} {⊥}

  -- The two variable layers of `φ⁻¹` fuse: swap-currying after folding `[ ⊥ , ⊥ ]₀ ≅ unit`.
  s : [ unit , unit ]₀ ⇒ [ ⊥ ⊗₀ unit , ⊥ ]₀
  s = _≅_.to sc ∘ [ id , ⊥to ]₁

  -- `φ⁻¹`'s inner map, merged: the double-dual `δ⇒` reindexed by `s`.
  m : ⊥ ⊗₀ unit ⇒ [ [ unit , unit ]₀ , ⊥ ]₀
  m = [ s , id ]₁ ∘ δ⇒ {A = ⊥ ⊗₀ unit}

  -- Covariant hom actions on a common source fuse.
  homˡ-∘ : {a : B ⇒ C} {b : A ⇒ B} → [ id {X} , a ]₁ ∘ [ id , b ]₁ ≈ [ id , a ∘ b ]₁
  homˡ-∘ = hom-∘ ○ [-,-].F-resp-≈ (identity² , Equiv.refl)

  -- `v₃⁻¹ ∘ v₂⁻¹` is the single hom action `[ s , id ]₁` (contravariant, so `s` reads in order).
  vv-fold : v₃⁻¹ {unit} ∘ v₂⁻¹ {unit} ∘ δ⇒ {A = ⊥ ⊗₀ unit} ≈ m
  vv-fold = sym-assoc ○ (hom-∘ᵣ ⟩∘⟨refl)

  -- `Ψ`'s three covariant layers merge to `[ id , m ]₁`.
  Ψ-fold : Ψ ≈ uncurry₂ ∘ [ id , m ]₁
  Ψ-fold = begin
    Ψ                                                              ≈⟨ refl⟩∘⟨ refl⟩∘⟨ homˡ-∘ ⟩
    uncurry₂ ∘ [ id , v₃⁻¹ {unit} ]₁ ∘ [ id , v₂⁻¹ {unit} ∘ δ⇒ ]₁  ≈⟨ refl⟩∘⟨ homˡ-∘ ⟩
    uncurry₂ ∘ [ id , v₃⁻¹ {unit} ∘ v₂⁻¹ {unit} ∘ δ⇒ ]₁            ≈⟨ refl⟩∘⟨ [-,-].F-resp-≈ (Equiv.refl , vv-fold) ⟩
    uncurry₂ ∘ [ id , m ]₁                                         ∎

  -- Uncurrying `Ψ = uncurry₂ ∘ [ id , m ]₁`: `uncurry₂`'s double eval, with `m` folded onto the
  -- inner one (`inner`, via `eval-comm-cod`).
  uncurryΨ : uncurry Ψ ≈ eval ∘ ((m ∘ eval) ⊗₁ id) ∘ α⇐
  uncurryΨ = begin
    eval ∘ (Ψ ⊗₁ id)                                   ≈⟨ refl⟩∘⟨ (Ψ-fold ⟩⊗⟨refl) ⟩
    eval ∘ ((uncurry₂ ∘ [ id , m ]₁) ⊗₁ id)            ≈⟨ refl⟩∘⟨ split₁ˡ ⟩
    eval ∘ (uncurry₂ ⊗₁ id) ∘ ([ id , m ]₁ ⊗₁ id)      ≈⟨ pullˡ eval-curry ⟩
    (uncurry eval ∘ α⇐) ∘ ([ id , m ]₁ ⊗₁ id)          ≈⟨ assoc ⟩
    uncurry eval ∘ α⇐ ∘ ([ id , m ]₁ ⊗₁ id)            ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩⊗⟨ ⟺ ⊗.identity) ⟩
    uncurry eval ∘ α⇐ ∘ ([ id , m ]₁ ⊗₁ (id ⊗₁ id))    ≈⟨ refl⟩∘⟨ assoc-commute-to ⟩
    uncurry eval ∘ (([ id , m ]₁ ⊗₁ id) ⊗₁ id) ∘ α⇐    ≈⟨ pullˡ inner ⟩
    (eval ∘ ((m ∘ eval) ⊗₁ id)) ∘ α⇐                   ≈⟨ assoc ⟩
    eval ∘ ((m ∘ eval) ⊗₁ id) ∘ α⇐                     ∎
    where
      inner : uncurry eval ∘ (([ id , m ]₁ ⊗₁ id) ⊗₁ id) ≈ eval ∘ ((m ∘ eval) ⊗₁ id)
      inner = begin
        (eval ∘ (eval ⊗₁ id)) ∘ (([ id , m ]₁ ⊗₁ id) ⊗₁ id)  ≈⟨ assoc ⟩
        eval ∘ (eval ⊗₁ id) ∘ (([ id , m ]₁ ⊗₁ id) ⊗₁ id)    ≈⟨ refl⟩∘⟨ merge₁ˡ ⟩
        eval ∘ ((eval ∘ ([ id , m ]₁ ⊗₁ id)) ⊗₁ id)          ≈⟨ refl⟩∘⟨ (eval-comm-cod ⟩⊗⟨refl) ⟩
        eval ∘ ((m ∘ eval) ⊗₁ id)                            ∎

  -- `α⇐` collapses `id ⊗₁ ρ⇐` at the unit into `ρ⇐ ⊗₁ id` (inverse triangle; `λ⇐ ≈ ρ⇐` at unit).
  αρ⇐ : α⇐ ∘ (id {X} ⊗₁ ρ⇐ {unit}) ≈ ρ⇐ {X} ⊗₁ id
  αρ⇐ = (refl⟩∘⟨ (refl⟩⊗⟨ ⟺ coherence-inv₃)) ○ triangle-inv

  -- `curry₂` on a name is the name of the curry: `curry₂ ∘ ⌜ g ⌝ ≈ ⌜ curry g ⌝` (double β + `coherence₁`).
  curry₂-name : {g : A ⊗₀ B ⇒ C} → curry₂ ∘ ⌜ g ⌝ ≈ ⌜ curry g ⌝
  curry₂-name {g = g} = uncurry²-injective (begin
    uncurry (uncurry (curry₂ ∘ ⌜ g ⌝))                    ≈⟨ uncurry-resp-≈ uncurry-∘ ⟩
    uncurry (uncurry curry₂ ∘ (⌜ g ⌝ ⊗₁ id))              ≈⟨ uncurry-∘ ⟩
    uncurry (uncurry curry₂) ∘ ((⌜ g ⌝ ⊗₁ id) ⊗₁ id)      ≈⟨ uncurry²-curry₂ ⟩∘⟨refl ⟩
    (eval ∘ α⇒) ∘ ((⌜ g ⌝ ⊗₁ id) ⊗₁ id)                  ≈⟨ pullʳ assoc-commute-from ⟩
    eval ∘ (⌜ g ⌝ ⊗₁ (id ⊗₁ id)) ∘ α⇒                    ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ ⊗.identity) ⟩∘⟨refl ⟩
    eval ∘ (⌜ g ⌝ ⊗₁ id) ∘ α⇒                            ≈⟨ pullˡ eval-⌜⌝ ⟩
    (g ∘ λ⇒) ∘ α⇒                                        ≈⟨ pullʳ coherence₁ ⟩
    g ∘ (λ⇒ ⊗₁ id)                                       ≈˘⟨ eval-curry ⟩∘⟨refl ⟩
    uncurry (curry g) ∘ (λ⇒ ⊗₁ id)                       ≈˘⟨ uncurry-∘ ⟩
    uncurry (curry g ∘ λ⇒)                               ≈˘⟨ uncurry-resp-≈ eval-⌜⌝ ⟩
    uncurry (uncurry ⌜ curry g ⌝)                        ∎)

  -- `⊥to`, a value of `[ ⊥ , ⊥ ]₀`, is `curry (ρ⇒ ∘ σ⇒)`.  It is `[ i⇒ , id ]₁ ∘ δ⇒` with
  -- `δ⇒ = curry (eval ∘ σ⇒)`; `hom-curryᵣ` folds `i⇒` inside, and `ρσ` rewrites `eval` past it.
  ρσ : ρ⇒ {⊥} ∘ σ⇒ ≈ (eval {unit} {⊥} ∘ σ⇒) ∘ (id ⊗₁ unit-hom⇒)
  ρσ = begin
    ρ⇒ ∘ σ⇒                             ≈˘⟨ eval-unit-hom⇒ ⟩∘⟨refl ⟩
    (eval ∘ (unit-hom⇒ ⊗₁ id)) ∘ σ⇒     ≈⟨ assoc ⟩
    eval ∘ (unit-hom⇒ ⊗₁ id) ∘ σ⇒       ≈˘⟨ refl⟩∘⟨ σ⇒-comm ⟩
    eval ∘ σ⇒ ∘ (id ⊗₁ unit-hom⇒)       ≈⟨ sym-assoc ⟩
    (eval ∘ σ⇒) ∘ (id ⊗₁ unit-hom⇒)     ∎

  ⊥to-fold : ⊥to ≈ curry (ρ⇒ {⊥} ∘ σ⇒)
  ⊥to-fold = begin
    [ unit-hom⇒ , id ]₁ ∘ curry (eval ∘ σ⇒)      ≈⟨ hom-curryᵣ ⟩
    curry ((eval ∘ σ⇒) ∘ (id ⊗₁ unit-hom⇒))      ≈˘⟨ curry-resp-≈ ρσ ⟩
    curry (ρ⇒ ∘ σ⇒)                              ∎

  -- The crux (Lemma 3.5's kernel).  Naming the identity, folding `[ ⊥ , ⊥ ]₀ ≅ unit`, then
  -- swap-currying, is the name of the right unitor.  Apply `swap`'s inverse: `swap.from ∘ ⌜ ρ⇒ ⌝`
  -- names `ρ⇒ ∘ σ⇒ = ⊥to`, so the two agree and `swap`'s iso cancels back to `⌜ ρ⇒ ⌝`.
  s-name : s ∘ ⌜id⌝ ≈ ⌜ ρ⇒ {⊥} ⌝
  s-name = begin
    s ∘ ⌜id⌝                                     ≈⟨ assoc ⟩
    _≅_.to sc ∘ [ id , ⊥to ]₁ ∘ ⌜id⌝             ≈⟨ refl⟩∘⟨ hom-curry ⟩
    _≅_.to sc ∘ curry (⊥to ∘ (id ∘ λ⇒) ∘ (id ⊗₁ id))
      ≈⟨ refl⟩∘⟨ curry-resp-≈ (refl⟩∘⟨ elimʳ ⊗.identity) ⟩
    _≅_.to sc ∘ curry (⊥to ∘ id ∘ λ⇒)            ≈⟨ refl⟩∘⟨ curry-resp-≈ (refl⟩∘⟨ identityˡ) ⟩
    _≅_.to sc ∘ ⌜ ⊥to ⌝                          ≈˘⟨ refl⟩∘⟨ from-name ⟩
    _≅_.to sc ∘ _≅_.from sc ∘ ⌜ ρ⇒ ⌝            ≈⟨ cancelˡ (_≅_.isoˡ sc) ⟩
    ⌜ ρ⇒ ⌝                                       ∎
    where
      -- `swap.from = curry₂ ∘ [ σ⇒ , id ]₁` (definitionally); on `⌜ ρ⇒ ⌝` it names `ρ⇒ ∘ σ⇒`,
      -- then `curry₂-name` folds the currying and `⊥to-fold` recognises the result as `⊥to`.
      from-name : _≅_.from sc ∘ ⌜ ρ⇒ {⊥} ⌝ ≈ ⌜ ⊥to ⌝
      from-name = begin
        _≅_.from sc ∘ ⌜ ρ⇒ ⌝                          ≈⟨ assoc ⟩
        curry₂ ∘ [ σ⇒ , id ]₁ ∘ ⌜ ρ⇒ ⌝               ≈⟨ refl⟩∘⟨ hom-curryᵣ ⟩
        curry₂ ∘ curry ((ρ⇒ ∘ λ⇒) ∘ (id ⊗₁ σ⇒))      ≈⟨ refl⟩∘⟨ curry-resp-≈ assoc ⟩
        curry₂ ∘ curry (ρ⇒ ∘ λ⇒ ∘ (id ⊗₁ σ⇒))        ≈⟨ refl⟩∘⟨ curry-resp-≈ (refl⟩∘⟨ unitorˡ-commute-from) ⟩
        curry₂ ∘ curry (ρ⇒ ∘ σ⇒ ∘ λ⇒)                ≈⟨ refl⟩∘⟨ curry-resp-≈ sym-assoc ⟩
        curry₂ ∘ ⌜ ρ⇒ ∘ σ⇒ ⌝                          ≈⟨ curry₂-name ⟩
        ⌜ curry (ρ⇒ ∘ σ⇒) ⌝                           ≈˘⟨ curry-resp-≈ (⊥to-fold ⟩∘⟨refl) ⟩
        ⌜ ⊥to ⌝                                        ∎

  -- `can`'s associator collapses to `ρ⇐ ⊗₁ ⌜id⌝` (inverse triangle `αρ⇐`).
  can-α : α⇐ ∘ (id {[ unit , ⊥ ⊗₀ unit ]₀} ⊗₁ can) ≈ ρ⇐ ⊗₁ ⌜id⌝
  can-α = begin
    α⇐ ∘ (id ⊗₁ can)                             ≈⟨ refl⟩∘⟨ split₂ˡ ⟩
    α⇐ ∘ (id ⊗₁ (id ⊗₁ ⌜id⌝)) ∘ (id ⊗₁ ρ⇐)      ≈⟨ pullˡ assoc-commute-to ⟩
    (((id ⊗₁ id) ⊗₁ ⌜id⌝) ∘ α⇐) ∘ (id ⊗₁ ρ⇐)    ≈⟨ assoc ⟩
    ((id ⊗₁ id) ⊗₁ ⌜id⌝) ∘ α⇐ ∘ (id ⊗₁ ρ⇐)      ≈⟨ refl⟩∘⟨ αρ⇐ ⟩
    ((id ⊗₁ id) ⊗₁ ⌜id⌝) ∘ (ρ⇐ ⊗₁ id)           ≈⟨ ⟺ ⊗.homomorphism ⟩
    ((id ⊗₁ id) ∘ ρ⇐) ⊗₁ (⌜id⌝ ∘ id)            ≈⟨ (elimˡ ⊗.identity) ⟩⊗⟨ identityʳ ⟩
    ρ⇐ ⊗₁ ⌜id⌝                                   ∎

  -- `m ∘ unit-hom⇐` is `curry gm`: `δ⇒ = curry (eval ∘ σ⇒)`, reindexed by `unit-hom⇐` and `s`.
  gm : [ unit , ⊥ ⊗₀ unit ]₀ ⊗₀ [ unit , unit ]₀ ⇒ ⊥
  gm = (eval ∘ σ⇒) ∘ (unit-hom⇐ ⊗₁ id) ∘ (id ⊗₁ s)
  m-curry : m ∘ unit-hom⇐ ≈ curry gm
  m-curry = begin
    m ∘ unit-hom⇐                                          ≈⟨ assoc ⟩
    [ s , id ]₁ ∘ δ⇒ ∘ unit-hom⇐                           ≈⟨ refl⟩∘⟨ ⟺ curry-∘ ⟩
    [ s , id ]₁ ∘ curry ((eval ∘ σ⇒) ∘ (unit-hom⇐ ⊗₁ id))  ≈⟨ hom-curryᵣ ⟩
    curry (((eval ∘ σ⇒) ∘ (unit-hom⇐ ⊗₁ id)) ∘ (id ⊗₁ s))  ≈⟨ curry-resp-≈ assoc ⟩
    curry gm                                               ∎

  -- Feeding `⌜id⌝` into `gm`: `s ∘ ⌜id⌝ = ⌜ ρ⇒ ⌝` (`s-name`) names the unitor, and the braid
  -- unwinds — `λ⇒ ∘ σ⇒ = ρ⇒` (`braiding-coherence`), `unit-hom⇐ ∘ ρ⇒ = eval` — to `ρ⇒ ∘ eval`.
  gm-feeds : gm ∘ (id ⊗₁ ⌜id⌝) ≈ ρ⇒ ∘ eval {unit} {⊥ ⊗₀ unit}
  gm-feeds = begin
    ((eval ∘ σ⇒) ∘ (unit-hom⇐ ⊗₁ id) ∘ (id ⊗₁ s)) ∘ (id ⊗₁ ⌜id⌝) ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ⟩
    (eval ∘ σ⇒) ∘ (unit-hom⇐ ⊗₁ id) ∘ (id ⊗₁ s) ∘ (id ⊗₁ ⌜id⌝)   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ merge₂ˡ ⟩
    (eval ∘ σ⇒) ∘ (unit-hom⇐ ⊗₁ id) ∘ (id ⊗₁ (s ∘ ⌜id⌝))         ≈⟨ refl⟩∘⟨ refl⟩∘⟨ (refl⟩⊗⟨ s-name) ⟩
    (eval ∘ σ⇒) ∘ (unit-hom⇐ ⊗₁ id) ∘ (id ⊗₁ ⌜ ρ⇒ ⌝)            ≈⟨ refl⟩∘⟨ ⟺ serialize₁₂ ⟩
    (eval ∘ σ⇒) ∘ (unit-hom⇐ ⊗₁ ⌜ ρ⇒ ⌝)                         ≈⟨ pullʳ σ⇒-comm ⟩
    eval ∘ (⌜ ρ⇒ ⌝ ⊗₁ unit-hom⇐) ∘ σ⇒                           ≈⟨ pullˡ eval-name ⟩
    (ρ⇒ ∘ unit-hom⇐ ∘ λ⇒) ∘ σ⇒                                  ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ⟩
    ρ⇒ ∘ unit-hom⇐ ∘ λ⇒ ∘ σ⇒                                    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ braiding-coherence ⟩
    ρ⇒ ∘ unit-hom⇐ ∘ ρ⇒                                         ≈⟨ refl⟩∘⟨ cancelʳ unitorʳ.isoˡ ⟩
    ρ⇒ ∘ eval                                                   ∎
    where
      eval-name : eval ∘ (⌜ ρ⇒ {⊥} ⌝ ⊗₁ unit-hom⇐) ≈ ρ⇒ ∘ unit-hom⇐ ∘ λ⇒
      eval-name = begin
        eval ∘ (⌜ ρ⇒ ⌝ ⊗₁ unit-hom⇐)               ≈⟨ refl⟩∘⟨ serialize₁₂ ⟩
        eval ∘ (⌜ ρ⇒ ⌝ ⊗₁ id) ∘ (id ⊗₁ unit-hom⇐)  ≈⟨ pullˡ eval-⌜⌝ ⟩
        (ρ⇒ ∘ λ⇒) ∘ (id ⊗₁ unit-hom⇐)              ≈⟨ pullʳ unitorˡ-commute-from ⟩
        ρ⇒ ∘ unit-hom⇐ ∘ λ⇒                        ∎

  -- The heart of Lemma 3.5: `Ψ` fed the canonical `can` evaluates to the right unitor.  Uncurry
  -- `Ψ` (`uncurryΨ`), collapse `can`'s associator (`can-α`), reduce `m ∘ unit-hom⇐ = curry gm`
  -- (`m-curry`) and feed `⌜id⌝` (`gm-feeds`).
  core : eval ∘ (Ψ ⊗₁ can) ≈ ρ⇒ ∘ eval {unit} {⊥ ⊗₀ unit}
  core = begin
    eval ∘ (Ψ ⊗₁ can)                                  ≈⟨ refl⟩∘⟨ serialize₁₂ ⟩
    eval ∘ (Ψ ⊗₁ id) ∘ (id ⊗₁ can)                     ≈⟨ sym-assoc ⟩
    (eval ∘ (Ψ ⊗₁ id)) ∘ (id ⊗₁ can)                   ≈⟨ uncurryΨ ⟩∘⟨refl ⟩
    (eval ∘ ((m ∘ eval) ⊗₁ id) ∘ α⇐) ∘ (id ⊗₁ can)     ≈⟨ assoc ○ (refl⟩∘⟨ assoc) ⟩
    eval ∘ ((m ∘ eval) ⊗₁ id) ∘ α⇐ ∘ (id ⊗₁ can)       ≈⟨ refl⟩∘⟨ refl⟩∘⟨ can-α ⟩
    eval ∘ ((m ∘ eval) ⊗₁ id) ∘ (ρ⇐ ⊗₁ ⌜id⌝)           ≈⟨ refl⟩∘⟨ ⟺ ⊗.homomorphism ⟩
    eval ∘ (((m ∘ eval) ∘ ρ⇐) ⊗₁ (id ∘ ⌜id⌝))          ≈⟨ refl⟩∘⟨ (assoc ⟩⊗⟨ identityˡ) ⟩
    eval ∘ ((m ∘ unit-hom⇐) ⊗₁ ⌜id⌝)                   ≈⟨ refl⟩∘⟨ (m-curry ⟩⊗⟨refl) ⟩
    eval ∘ (curry gm ⊗₁ ⌜id⌝)                          ≈⟨ refl⟩∘⟨ serialize₁₂ ⟩
    eval ∘ (curry gm ⊗₁ id) ∘ (id ⊗₁ ⌜id⌝)             ≈⟨ pullˡ eval-curry ⟩
    gm ∘ (id ⊗₁ ⌜id⌝)                                  ≈⟨ gm-feeds ⟩
    ρ⇒ ∘ eval                                          ∎

  -- Lemma 3.5's kernel: `φ⁻¹ ∘ can` names `τ {unit}`.  `[ Ψ , id ]₁ ∘ δ⇒ ∘ can` is a `curry`
  -- (`hom-curryᵣ`); braiding turns its content into `eval ∘ (Ψ ⊗₁ can) = ρ⇒ ∘ eval` (`core`),
  -- which `τρ` and `braiding-coherence′` recognise as `τ ∘ λ⇒`, i.e. `⌜ τ ⌝`.
  φ⇐-can : φ⇐ ∘ can ≈ ⌜ τ {unit} {⊥} ⌝
  φ⇐-can = begin
    φ⇐ ∘ can                                           ≈⟨ φ⇐-merge ⟩∘⟨refl ⟩
    ([ Ψ , id ]₁ ∘ δ⇒) ∘ can                           ≈⟨ assoc ⟩
    [ Ψ , id ]₁ ∘ δ⇒ ∘ can                             ≈⟨ refl⟩∘⟨ ⟺ curry-∘ ⟩
    [ Ψ , id ]₁ ∘ curry ((eval ∘ σ⇒) ∘ (can ⊗₁ id))    ≈⟨ hom-curryᵣ ⟩
    curry (((eval ∘ σ⇒) ∘ (can ⊗₁ id)) ∘ (id ⊗₁ Ψ))    ≈⟨ curry-resp-≈ names ⟩
    ⌜ τ ⌝                                              ∎
    where
      names : ((eval ∘ σ⇒) ∘ (can ⊗₁ id)) ∘ (id ⊗₁ Ψ) ≈ τ {unit} {⊥} ∘ λ⇒
      names = begin
        ((eval ∘ σ⇒) ∘ (can ⊗₁ id)) ∘ (id ⊗₁ Ψ)  ≈⟨ assoc ○ (refl⟩∘⟨ ⟺ serialize₁₂) ⟩
        (eval ∘ σ⇒) ∘ (can ⊗₁ Ψ)                  ≈⟨ assoc ⟩
        eval ∘ σ⇒ ∘ (can ⊗₁ Ψ)                    ≈⟨ refl⟩∘⟨ σ⇒-comm ⟩
        eval ∘ (Ψ ⊗₁ can) ∘ σ⇒                    ≈⟨ pullˡ core ⟩
        (ρ⇒ ∘ eval) ∘ σ⇒                          ≈˘⟨ τρ ⟩∘⟨refl ⟩
        (τ ∘ ρ⇒) ∘ σ⇒                             ≈⟨ assoc ⟩
        τ ∘ ρ⇒ ∘ σ⇒                               ≈⟨ refl⟩∘⟨ braiding-coherence′ ⟩
        τ ∘ λ⇒                                    ∎

  -- Lemma 3.5.  `t {unit}` is the canonical `can`: `φ` is an iso and `φ⁻¹ ∘ can = τ̂` (`φ⇐-can`).
  t-unit : t {unit} ≈ (id ⊗₁ ⌜id⌝) ∘ ρ⇐
  t-unit = begin
    φ⇒ unit unit ∘ τ̂ {unit} {⊥}   ≈˘⟨ refl⟩∘⟨ φ⇐-can ⟩
    φ⇒ unit unit ∘ φ⇐ ∘ can       ≈⟨ cancelˡ (_≅_.isoʳ (φ-≅ {unit} {unit})) ⟩
    can                           ∎

  φ-comm₁ : {X Y : Obj} {f : X ⇒ Y} → (f ⊗₁ id) ∘ φ⇒ X X ≈ φ⇒ Y X ∘ [ [ f , id ]₁ , id ]₁
  φ-comm₁ {X} {Y} {f} = begin
    (f ⊗₁ id) ∘ φ⇒ X X                    ≈˘⟨ (refl⟩⊗⟨ [-,-].identity) ⟩∘⟨refl ⟩
    (f ⊗₁ [ id , id ]₁) ∘ φ⇒ X X          ≈˘⟨ NaturalIsomorphism.⇒.commute φ-NI (f , id) ⟩
    φ⇒ Y X ∘ [ [ f , id ⊗₁ id ]₁ , id ]₁  ≈⟨ refl⟩∘⟨ [-,-].F-resp-≈ ([-,-].F-resp-≈ (Equiv.refl , ⊗.identity) , Equiv.refl) ⟩
    φ⇒ Y X ∘ [ [ f , id ]₁ , id ]₁        ∎

  φ-comm₂ : {X Y : Obj} {f : X ⇒ Y} → (id ⊗₁ [ f , id ]₁) ∘ φ⇒ Y Y ≈ φ⇒ Y X ∘ [ [ id , id ⊗₁ f ]₁ , id ]₁
  φ-comm₂ {X} {Y} {f} =
    ⟺ (NaturalIsomorphism.⇒.commute φ-NI (id , f))

  -- Dualizing a map `p` and feeding it a name pre-composes the named map: `⌜ h ⌝ = curry (h ∘ λ⇒)`,
  -- `hom-curryᵣ` folds `p` inside, and the left unitor slides past it (`unitorˡ-commute-from`).
  name-precompose : {p : A ⇒ B} {h : B ⇒ ⊥} → [ p , id {⊥} ]₁ ∘ ⌜ h ⌝ ≈ ⌜ h ∘ p ⌝
  name-precompose {p = p} {h = h} = begin
    [ p , id ]₁ ∘ ⌜ h ⌝            ≈⟨ hom-curryᵣ ⟩
    curry ((h ∘ λ⇒) ∘ (id ⊗₁ p))   ≈⟨ curry-resp-≈ assoc ⟩
    curry (h ∘ λ⇒ ∘ (id ⊗₁ p))     ≈⟨ curry-resp-≈ (refl⟩∘⟨ unitorˡ-commute-from) ⟩
    curry (h ∘ p ∘ λ⇒)             ≈⟨ curry-resp-≈ sym-assoc ⟩
    ⌜ h ∘ p ⌝                      ∎

  -- The extranaturality of the unit in wire form: precomposing `f` on the `X`-strand equals
  -- reindexing the dual on the `X *`-strand.  This is `τ`'s dinaturality (Lemma 3.1) carried
  -- across `φ`'s naturality (Lemma 3.2): both `φ-comm`s move the reindexing onto the name of
  -- `τ`, where `name-precompose` and `τ-dinatural` swap `[ f , id ]₁` for `[ id , id ⊗₁ f ]₁`.
  t-wire : {f : X ⇒ Y} → (f ⊗₁ id) ∘ t {X} ≈ (id ⊗₁ [ f , id ]₁) ∘ t {Y}
  t-wire {X} {Y} {f} = begin
    (f ⊗₁ id) ∘ φ⇒ X X ∘ ⌜ τ ⌝               ≈⟨ pullˡ φ-comm₁ ⟩
    (φ⇒ Y X ∘ [ [ f , id ]₁ , id ]₁) ∘ ⌜ τ ⌝  ≈⟨ assoc ⟩
    φ⇒ Y X ∘ [ [ f , id ]₁ , id ]₁ ∘ ⌜ τ ⌝   ≈⟨ refl⟩∘⟨ name-precompose ⟩
    φ⇒ Y X ∘ ⌜ τ ∘ [ f , id ]₁ ⌝             ≈˘⟨ refl⟩∘⟨ curry-resp-≈ (τ-dinatural ⟩∘⟨refl) ⟩
    φ⇒ Y X ∘ ⌜ τ ∘ [ id , id ⊗₁ f ]₁ ⌝       ≈˘⟨ refl⟩∘⟨ name-precompose ⟩
    φ⇒ Y X ∘ [ [ id , id ⊗₁ f ]₁ , id ]₁ ∘ ⌜ τ ⌝  ≈˘⟨ assoc ⟩
    (φ⇒ Y X ∘ [ [ id , id ⊗₁ f ]₁ , id ]₁) ∘ ⌜ τ ⌝  ≈˘⟨ φ-comm₂ ⟩∘⟨refl ⟩
    ((id ⊗₁ [ f , id ]₁) ∘ φ⇒ Y Y) ∘ ⌜ τ ⌝   ≈⟨ assoc ⟩
    (id ⊗₁ [ f , id ]₁) ∘ φ⇒ Y Y ∘ ⌜ τ ⌝     ∎

