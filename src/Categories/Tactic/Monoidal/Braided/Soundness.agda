{-# OPTIONS --safe --without-K #-}


open import Level using (Level)
open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Braided using (Braided)

module Categories.Tactic.Monoidal.Braided.Soundness
  {o ℓ e a : Level}
  {𝒞 : Category o ℓ e}
  {V : Monoidal 𝒞}
  (B : Braided V)
  {Atom : Set a}
  (⟦_⟧ₐ : Atom → Category.Obj 𝒞)
  where

open import Data.Product using (_,_)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; cong) renaming (refl to ≡refl)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; ↭-reflexive; ↭-sym; refl; prep; swap; trans)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (++⁺ˡ; ++⁺ʳ; ++⁺)

open import Categories.Tactic.Monoidal.Free using (module Free)
open import Categories.Tactic.Monoidal.Braided
  using (module FreeBraided; module Evaluation; ⇒⇒perm; shift; ++-swap)
open import Categories.Tactic.Monoidal.Braided.AdjacentSwaps B ⟦_⟧ₐ
  using (swap₁; swap₁-μ; swap₁-hexagon; swap₁-naturalʳ)

open import Categories.Tactic.Monoidal.Core V ⟦_⟧ₐ
  using (⟦_⟧₀; ⟦_⟧₁) renaming (eval to ⟦_⟧ᴹ; strictify to strict)
open import Categories.Morphism 𝒞 using (_≅_)
open import Categories.Tactic.Monoidal.Coherence V ⟦_⟧ₐ
  using (substₑ; substₑ-cons)
  renaming
    ( κ⁻¹ to strict⁻¹
    ; κ⁻¹-natural to strict⁻¹-natural
    ; μ⇒ to μ
    )
open Evaluation B ⟦_⟧ₐ using (⟦_⟧ᵇ; σ⇒)

open Category 𝒞
open Monoidal V using (_⊗₀_; _⊗₁_; unit; associator; unitorˡ; unitorʳ; triangle;
  unitorˡ-commute-to; assoc-commute-to; assoc-commute-from; module ⊗)
open Braided B using (braiding; hexagon₁; hexagon₂)
open import Categories.Category.Monoidal.Reasoning V
open import Categories.Category.Monoidal.Utilities V using (module Shorthands; triangle-inv)
open Shorthands
open import Categories.Category.Monoidal.Properties V using (module Kelly's)
open Kelly's using (coherence-inv₁; coherence-inv₂; coherence-inv₃)
import Categories.Category.Monoidal.Braided.Properties as BraidedProperties
open BraidedProperties B using (braiding-coherence; inv-Braided)
module InvBraidedProperties = BraidedProperties inv-Braided
open import Categories.Morphism.Reasoning 𝒞
  using (assoc²βε; pullˡ; pullʳ; elimˡ; elimʳ; module Cancellers; module Switch)
open Free Atom using () renaming
  ( _⇒_ to _⇒ᵐ_; ⇒⇒nf to ⇒⇒nfᵐ; idₘ to idᵐ
  ; α⇒ to α⇒ᵐ; α⇐ to α⇐ᵐ; λ⇒ to λ⇒ᵐ; λ⇐ to λ⇐ᵐ; ρ⇒ to ρ⇒ᵐ; ρ⇐ to ρ⇐ᵐ )
open FreeBraided Atom renaming
  ( α⇒ to α⇒ᵇ; α⇐ to α⇐ᵇ; λ⇒ to λ⇒ᵇ
  ; λ⇐ to λ⇐ᵇ; ρ⇒ to ρ⇒ᵇ; ρ⇐ to ρ⇐ᵇ )

private
  id₃ : ∀ {X Y Z} → id {X} ⊗₁ (id {Y} ⊗₁ id {Z}) ≈ id {X ⊗₀ (Y ⊗₀ Z)}
  id₃ {X} {Y} {Z} = begin
    id {X} ⊗₁ (id {Y} ⊗₁ id {Z})
      ≈⟨ refl⟩⊗⟨ ⊗.identity ⟩
    id {X} ⊗₁ id {Y ⊗₀ Z}
      ≈⟨ ⊗.identity ⟩
    id {X ⊗₀ (Y ⊗₀ Z)}
      ∎

  σρ-factor : ∀ {A X} →
    (σ⇒ {A} {unit} ⊗₁ id {X}) ∘ (ρ⇐ {A} ⊗₁ id {X})
    ≈ (σ⇒ {A} {unit} ∘ ρ⇐ {A}) ⊗₁ id {X}
  σρ-factor = begin
    (σ⇒ ⊗₁ id) ∘ (ρ⇐ ⊗₁ id)
      ≈˘⟨ ⊗-distrib-over-∘ ⟩
    (σ⇒ ∘ ρ⇐) ⊗₁ (id ∘ id)
      ≈⟨ Equiv.refl ⟩⊗⟨ identity² ⟩
    (σ⇒ ∘ ρ⇐) ⊗₁ id
      ∎

  σ-unitʳ : ∀ {A} → σ⇒ {A} {unit} ∘ ρ⇐ ≈ λ⇐
  σ-unitʳ {A} = begin
    σ⇒ {A} {unit} ∘ ρ⇐ {A}
      ≈˘⟨ identityˡ ⟩
    id ∘ (σ⇒ {A} {unit} ∘ ρ⇐ {A})
      ≈˘⟨ unitorˡ.isoˡ ⟩∘⟨refl ⟩
    (λ⇐ ∘ λ⇒) ∘ (σ⇒ {A} {unit} ∘ ρ⇐ {A})
      ≈⟨ assoc ⟩
    λ⇐ ∘ (λ⇒ ∘ (σ⇒ {A} {unit} ∘ ρ⇐ {A}))
      ≈⟨ refl⟩∘⟨ sym-assoc ⟩
    λ⇐ ∘ ((λ⇒ ∘ σ⇒ {A} {unit}) ∘ ρ⇐ {A})
      ≈⟨ refl⟩∘⟨ (braiding-coherence ⟩∘⟨refl) ⟩
    λ⇐ ∘ (ρ⇒ ∘ ρ⇐ {A})
      ≈⟨ refl⟩∘⟨ unitorʳ.isoʳ ⟩
    λ⇐ ∘ id
      ≈⟨ identityʳ ⟩
    λ⇐
      ∎

realize↭ : ∀ {xs ys : List Atom} → xs ↭ ys → ⟦ xs ⟧ᴹ ⇒ ⟦ ys ⟧ᴹ
realize↭ refl          = id
realize↭ (prep x p)    = id ⊗₁ realize↭ p
realize↭ (swap x y p)  =
  (id ⊗₁ (id ⊗₁ realize↭ p))
    ∘ α⇒
    ∘ (σ⇒ {⟦ x ⟧ₐ} {⟦ y ⟧ₐ} ⊗₁ id)
    ∘ α⇐
realize↭ (trans p q)   = realize↭ q ∘ realize↭ p

-- Reflexive permutation witnesses realize as interpretation coercions.
realize↭-reflexive : {xs ys : List Atom} (p : xs ≡ ys)
  → realize↭ (↭-reflexive p) ≈ substₑ p
realize↭-reflexive ≡refl = Equiv.refl

-- `realize↭` sends the reversal of a reflexive witness to the reversed coercion.
realize↭-sym-reflexive : {xs ys : List Atom} (p : xs ≡ ys)
  → realize↭ (↭-sym (↭-reflexive p)) ≈ substₑ (sym p)
realize↭-sym-reflexive ≡refl = Equiv.refl

struct-sound : ∀ {X Y} (f : X ⇒ᵐ Y)
  → ⟦ f ⟧₁ ∘ strict⁻¹ X ≈ strict⁻¹ Y ∘ realize↭ (↭-reflexive (⇒⇒nfᵐ f))
struct-sound {X} {Y} f = begin
  ⟦ f ⟧₁ ∘ strict⁻¹ X
    ≈⟨ strict⁻¹-natural f ⟩
  strict⁻¹ Y ∘ substₑ (⇒⇒nfᵐ f)
    ≈˘⟨ refl⟩∘⟨ realize↭-reflexive (⇒⇒nfᵐ f) ⟩
  strict⁻¹ Y ∘ realize↭ (↭-reflexive (⇒⇒nfᵐ f))
    ∎

-- Whiskering through the left half of `μ`.
μ-realizeˡ : (xs : List Atom) {ys zs : List Atom} (q : ys ↭ zs)
  → (id {⟦ xs ⟧ᴹ} ⊗₁ realize↭ q) ∘ μ xs ys ≈ μ xs zs ∘ realize↭ (++⁺ˡ xs q)
μ-realizeˡ []       q = ⟺ unitorˡ-commute-to
μ-realizeˡ (x ∷ xs) {ys} {zs} q = begin
  (id ⊗₁ realize↭ q) ∘ (α⇐ ∘ (id ⊗₁ μ xs ys))
    ≈⟨ (⟺ ⊗.identity ⟩⊗⟨refl) ⟩∘⟨refl ⟩
  ((id ⊗₁ id) ⊗₁ realize↭ q) ∘ (α⇐ ∘ (id ⊗₁ μ xs ys))
    ≈⟨ pullˡ (⟺ assoc-commute-to) ⟩
  (α⇐ ∘ (id ⊗₁ (id ⊗₁ realize↭ q))) ∘ (id ⊗₁ μ xs ys)
    ≈⟨ pullʳ (⟺ split₂ˡ) ⟩
  α⇐ ∘ (id ⊗₁ ((id ⊗₁ realize↭ q) ∘ μ xs ys))
    ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ μ-realizeˡ xs q ⟩
  α⇐ ∘ (id ⊗₁ (μ xs zs ∘ realize↭ (++⁺ˡ xs q)))
    ≈⟨ refl⟩∘⟨ split₂ˡ ⟩
  α⇐ ∘ (id ⊗₁ μ xs zs) ∘ (id ⊗₁ realize↭ (++⁺ˡ xs q))
    ≈⟨ sym-assoc ⟩
  (α⇐ ∘ (id ⊗₁ μ xs zs)) ∘ (id ⊗₁ realize↭ (++⁺ˡ xs q)) ∎

-- Whiskering through the right half of `μ`.
μ-realizeʳ : {xs xs' : List Atom} (p : xs ↭ xs') (ys : List Atom)
  → (realize↭ p ⊗₁ id {⟦ ys ⟧ᴹ}) ∘ μ xs ys ≈ μ xs' ys ∘ realize↭ (++⁺ʳ ys p)
μ-realizeʳ {xs} refl ys = begin
  (id ⊗₁ id) ∘ μ xs ys   ≈⟨ ⊗.identity ⟩∘⟨refl ⟩
  id ∘ μ xs ys           ≈⟨ identityˡ ⟩
  μ xs ys                ≈˘⟨ identityʳ ⟩
  μ xs ys ∘ id           ∎
μ-realizeʳ (prep {cs} {cs'} a p) ys = begin
  ((id ⊗₁ realize↭ p) ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ μ cs ys))
    ≈⟨ pullˡ (⟺ assoc-commute-to) ⟩
  (α⇐ ∘ (id ⊗₁ (realize↭ p ⊗₁ id))) ∘ (id ⊗₁ μ cs ys)
    ≈⟨ pullʳ (⟺ split₂ˡ) ⟩
  α⇐ ∘ (id ⊗₁ ((realize↭ p ⊗₁ id) ∘ μ cs ys))
    ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ μ-realizeʳ p ys ⟩
  α⇐ ∘ (id ⊗₁ (μ cs' ys ∘ realize↭ (++⁺ʳ ys p)))
    ≈⟨ refl⟩∘⟨ split₂ˡ ⟩
  α⇐ ∘ (id ⊗₁ μ cs' ys) ∘ (id ⊗₁ realize↭ (++⁺ʳ ys p))
    ≈⟨ sym-assoc ⟩
  (α⇐ ∘ (id ⊗₁ μ cs' ys)) ∘ (id ⊗₁ realize↭ (++⁺ʳ ys p)) ∎
μ-realizeʳ (swap {cs} {cs'} a b p) ys = begin
  (realize↭ (swap a b p) ⊗₁ id) ∘ μ (a ∷ b ∷ cs) ys
    ≈⟨ split₁ˡ ⟩∘⟨refl ⟩
  (((id ⊗₁ (id ⊗₁ realize↭ p)) ⊗₁ id) ∘ (swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ ⟦ cs ⟧ᴹ ⊗₁ id)) ∘ μ (a ∷ b ∷ cs) ys
    ≈⟨ assoc ⟩
  ((id ⊗₁ (id ⊗₁ realize↭ p)) ⊗₁ id) ∘ ((swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ ⟦ cs ⟧ᴹ ⊗₁ id) ∘ μ (a ∷ b ∷ cs) ys)
    ≈⟨ refl⟩∘⟨ swap₁-μ a b cs ys ⟩
  ((id ⊗₁ (id ⊗₁ realize↭ p)) ⊗₁ id) ∘ (μ (b ∷ a ∷ cs) ys ∘ swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ ⟦ cs ++ ys ⟧ᴹ)
    ≈⟨ pullˡ pp ⟩
  (μ (b ∷ a ∷ cs') ys ∘ (id ⊗₁ (id ⊗₁ realize↭ (++⁺ʳ ys p)))) ∘ swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ ⟦ cs ++ ys ⟧ᴹ
    ≈⟨ assoc ⟩
  μ (b ∷ a ∷ cs') ys ∘ ((id ⊗₁ (id ⊗₁ realize↭ (++⁺ʳ ys p))) ∘ swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ ⟦ cs ++ ys ⟧ᴹ) ∎
  where
    -- Slide the suffix realization through the two leading atoms.
    inner : ((id ⊗₁ realize↭ p) ⊗₁ id {⟦ ys ⟧ᴹ}) ∘ μ (a ∷ cs) ys
          ≈ μ (a ∷ cs') ys ∘ (id ⊗₁ realize↭ (++⁺ʳ ys p))
    inner = begin
      ((id ⊗₁ realize↭ p) ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ μ cs ys))
        ≈⟨ pullˡ (⟺ assoc-commute-to) ⟩
      (α⇐ ∘ (id ⊗₁ (realize↭ p ⊗₁ id))) ∘ (id ⊗₁ μ cs ys)
        ≈⟨ pullʳ (⟺ split₂ˡ) ⟩
      α⇐ ∘ (id ⊗₁ ((realize↭ p ⊗₁ id) ∘ μ cs ys))
        ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ μ-realizeʳ p ys ⟩
      α⇐ ∘ (id ⊗₁ (μ cs' ys ∘ realize↭ (++⁺ʳ ys p)))
        ≈⟨ refl⟩∘⟨ split₂ˡ ⟩
      α⇐ ∘ (id ⊗₁ μ cs' ys) ∘ (id ⊗₁ realize↭ (++⁺ʳ ys p))
        ≈⟨ sym-assoc ⟩
      (α⇐ ∘ (id ⊗₁ μ cs' ys)) ∘ (id ⊗₁ realize↭ (++⁺ʳ ys p)) ∎

    pp : ((id ⊗₁ (id ⊗₁ realize↭ p)) ⊗₁ id {⟦ ys ⟧ᴹ}) ∘ μ (b ∷ a ∷ cs) ys
       ≈ μ (b ∷ a ∷ cs') ys ∘ (id ⊗₁ (id ⊗₁ realize↭ (++⁺ʳ ys p)))
    pp = begin
      ((id ⊗₁ (id ⊗₁ realize↭ p)) ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ μ (a ∷ cs) ys))
        ≈⟨ pullˡ (⟺ assoc-commute-to) ⟩
      (α⇐ ∘ (id ⊗₁ ((id ⊗₁ realize↭ p) ⊗₁ id))) ∘ (id ⊗₁ μ (a ∷ cs) ys)
        ≈⟨ pullʳ (⟺ split₂ˡ) ⟩
      α⇐ ∘ (id ⊗₁ (((id ⊗₁ realize↭ p) ⊗₁ id) ∘ μ (a ∷ cs) ys))
        ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ inner ⟩
      α⇐ ∘ (id ⊗₁ (μ (a ∷ cs') ys ∘ (id ⊗₁ realize↭ (++⁺ʳ ys p))))
        ≈⟨ refl⟩∘⟨ split₂ˡ ⟩
      α⇐ ∘ (id ⊗₁ μ (a ∷ cs') ys) ∘ (id ⊗₁ (id ⊗₁ realize↭ (++⁺ʳ ys p)))
        ≈⟨ sym-assoc ⟩
      (α⇐ ∘ (id ⊗₁ μ (a ∷ cs') ys)) ∘ (id ⊗₁ (id ⊗₁ realize↭ (++⁺ʳ ys p))) ∎
μ-realizeʳ (trans {xs} {mid} {xs'} p₁ p₂) ys = begin
  ((realize↭ p₂ ∘ realize↭ p₁) ⊗₁ id) ∘ μ xs ys
    ≈⟨ split₁ˡ ⟩∘⟨refl ⟩
  ((realize↭ p₂ ⊗₁ id) ∘ (realize↭ p₁ ⊗₁ id)) ∘ μ xs ys
    ≈⟨ pullʳ (μ-realizeʳ p₁ ys) ⟩
  (realize↭ p₂ ⊗₁ id) ∘ (μ mid ys ∘ realize↭ (++⁺ʳ ys p₁))
    ≈⟨ pullˡ (μ-realizeʳ p₂ ys) ⟩
  (μ xs' ys ∘ realize↭ (++⁺ʳ ys p₂)) ∘ realize↭ (++⁺ʳ ys p₁)
    ≈⟨ assoc ⟩
  μ xs' ys ∘ (realize↭ (++⁺ʳ ys p₂) ∘ realize↭ (++⁺ʳ ys p₁)) ∎

-- Realization respects tensor.
μ-realize : {xs xs' ys ys' : List Atom} (p : xs ↭ xs') (q : ys ↭ ys')
  → (realize↭ p ⊗₁ realize↭ q) ∘ μ xs ys ≈ μ xs' ys' ∘ realize↭ (++⁺ p q)
μ-realize {xs} {xs'} {ys} {ys'} p q = begin
  (realize↭ p ⊗₁ realize↭ q) ∘ μ xs ys
    ≈⟨ serialize₂₁ ⟩∘⟨refl ⟩
  ((id ⊗₁ realize↭ q) ∘ (realize↭ p ⊗₁ id)) ∘ μ xs ys
    ≈⟨ pullʳ (μ-realizeʳ p ys) ⟩
  (id ⊗₁ realize↭ q) ∘ (μ xs' ys ∘ realize↭ (++⁺ʳ ys p))
    ≈⟨ pullˡ (μ-realizeˡ xs' q) ⟩
  (μ xs' ys' ∘ realize↭ (++⁺ˡ xs' q)) ∘ realize↭ (++⁺ʳ ys p)
    ≈⟨ assoc ⟩
  μ xs' ys' ∘ (realize↭ (++⁺ˡ xs' q) ∘ realize↭ (++⁺ʳ ys p)) ∎

-- `swap a b refl` realizes as `swap₁` on the leading pair.
realize-swap : (a b : Atom) (xs : List Atom) →
  realize↭ (swap a b (refl {xs = xs})) ≈ swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ ⟦ xs ⟧ᴹ
realize-swap a b xs = begin
  realize↭ (swap a b (refl {xs = xs}))
    ≈⟨ elimˡ id₃ ⟩
  swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ ⟦ xs ⟧ᴹ
    ∎

-- Braiding an atom past a block, transported through `μ`.
braid-atom : (a : Atom) (bs tl : List Atom)
  → swap₁ ⟦ a ⟧ₐ ⟦ bs ⟧ᴹ ⟦ tl ⟧ᴹ ∘ (id ⊗₁ μ bs tl)
    ≈ μ bs (a ∷ tl) ∘ realize↭ (↭-sym (shift a bs tl))
braid-atom a []        tl = begin
  swap₁ ⟦ a ⟧ₐ unit ⟦ tl ⟧ᴹ ∘ (id ⊗₁ λ⇐)
    ≈⟨ assoc²βε ⟩
  α⇒ ∘ (σ⇒ ⊗₁ id) ∘ (α⇐ ∘ (id ⊗₁ λ⇐))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ triangle-inv ⟩
  α⇒ ∘ (σ⇒ ⊗₁ id) ∘ (ρ⇐ ⊗₁ id)
    ≈⟨ refl⟩∘⟨ σρ-factor ⟩
  α⇒ ∘ ((σ⇒ ∘ ρ⇐) ⊗₁ id)
    ≈⟨ refl⟩∘⟨ (σ-unitʳ ⟩⊗⟨refl) ⟩
  α⇒ ∘ (λ⇐ ⊗₁ id)
    ≈⟨ refl⟩∘⟨ (⟺ coherence-inv₁) ⟩
  α⇒ ∘ (α⇐ ∘ λ⇐)
    ≈⟨ Cancellers.cancelˡ associator.isoʳ ⟩
  λ⇐
    ≈˘⟨ identityʳ ⟩
  λ⇐ ∘ id ∎
braid-atom a (b ∷ bs') tl = begin
  swap₁ ⟦ a ⟧ₐ ⟦ b ∷ bs' ⟧ᴹ ⟦ tl ⟧ᴹ ∘ (id ⊗₁ μ (b ∷ bs') tl)
    ≈⟨ refl⟩∘⟨ split₂ˡ ⟩
  swap₁ ⟦ a ⟧ₐ (⟦ b ⟧ₐ ⊗₀ ⟦ bs' ⟧ᴹ) ⟦ tl ⟧ᴹ ∘ ((id ⊗₁ α⇐) ∘ (id ⊗₁ (id ⊗₁ μ bs' tl)))
    ≈⟨ pullˡ (swap₁-hexagon {⟦ a ⟧ₐ} {⟦ b ⟧ₐ} {⟦ bs' ⟧ᴹ} {⟦ tl ⟧ᴹ}) ⟩
  (α⇐ ∘ (id ⊗₁ swap₁ ⟦ a ⟧ₐ ⟦ bs' ⟧ᴹ ⟦ tl ⟧ᴹ) ∘ swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ (⟦ bs' ⟧ᴹ ⊗₀ ⟦ tl ⟧ᴹ))
    ∘ (id ⊗₁ (id ⊗₁ μ bs' tl))
    ≈⟨ assoc²βε ⟩
  α⇐ ∘ (id ⊗₁ swap₁ ⟦ a ⟧ₐ ⟦ bs' ⟧ᴹ ⟦ tl ⟧ᴹ)
    ∘ (swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ (⟦ bs' ⟧ᴹ ⊗₀ ⟦ tl ⟧ᴹ) ∘ (id ⊗₁ (id ⊗₁ μ bs' tl)))
    ≈⟨ refl⟩∘⟨ refl⟩∘⟨ swap₁-naturalʳ (μ bs' tl) ⟩
  α⇐ ∘ (id ⊗₁ swap₁ ⟦ a ⟧ₐ ⟦ bs' ⟧ᴹ ⟦ tl ⟧ᴹ)
    ∘ ((id ⊗₁ (id ⊗₁ μ bs' tl)) ∘ swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ ⟦ bs' ++ tl ⟧ᴹ)
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  α⇐ ∘ ((id ⊗₁ swap₁ ⟦ a ⟧ₐ ⟦ bs' ⟧ᴹ ⟦ tl ⟧ᴹ) ∘ (id ⊗₁ (id ⊗₁ μ bs' tl)))
    ∘ swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ ⟦ bs' ++ tl ⟧ᴹ
    ≈⟨ refl⟩∘⟨ (⟺ split₂ˡ) ⟩∘⟨refl ⟩
  α⇐ ∘ (id ⊗₁ (swap₁ ⟦ a ⟧ₐ ⟦ bs' ⟧ᴹ ⟦ tl ⟧ᴹ ∘ (id ⊗₁ μ bs' tl)))
    ∘ swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ ⟦ bs' ++ tl ⟧ᴹ
    ≈⟨ refl⟩∘⟨ (refl⟩⊗⟨ braid-atom a bs' tl) ⟩∘⟨refl ⟩
  α⇐ ∘ (id ⊗₁ (μ bs' (a ∷ tl) ∘ realize↭ (↭-sym (shift a bs' tl))))
    ∘ swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ ⟦ bs' ++ tl ⟧ᴹ
    ≈⟨ refl⟩∘⟨ split₂ˡ ⟩∘⟨refl ⟩
  α⇐ ∘ ((id ⊗₁ μ bs' (a ∷ tl)) ∘ (id ⊗₁ realize↭ (↭-sym (shift a bs' tl))))
    ∘ swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ ⟦ bs' ++ tl ⟧ᴹ
    ≈⟨ refl⟩∘⟨ assoc ⟩
  α⇐ ∘ ((id ⊗₁ μ bs' (a ∷ tl))
    ∘ ((id ⊗₁ realize↭ (↭-sym (shift a bs' tl))) ∘ swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ ⟦ bs' ++ tl ⟧ᴹ))
    ≈⟨ sym-assoc ⟩
  (α⇐ ∘ (id ⊗₁ μ bs' (a ∷ tl)))
    ∘ ((id ⊗₁ realize↭ (↭-sym (shift a bs' tl))) ∘ swap₁ ⟦ a ⟧ₐ ⟦ b ⟧ₐ ⟦ bs' ++ tl ⟧ᴹ)
    ≈˘⟨ refl⟩∘⟨ (refl⟩∘⟨ realize-swap a b (bs' ++ tl)) ⟩
  (α⇐ ∘ (id ⊗₁ μ bs' (a ∷ tl)))
    ∘ ((id ⊗₁ realize↭ (↭-sym (shift a bs' tl))) ∘ realize↭ (swap a b (refl {xs = bs' ++ tl}))) ∎

-- Left-unit form of `braiding-coherence`.
braid-unitˡ : ∀ {Y} → σ⇒ {unit} {Y} ∘ λ⇐ ≈ ρ⇐
braid-unitˡ = begin
  σ⇒ ∘ λ⇐
    ≈˘⟨ Cancellers.cancelˡ unitorʳ.isoˡ ⟩
  ρ⇐ ∘ (ρ⇒ ∘ (σ⇒ ∘ λ⇐))
    ≈⟨ refl⟩∘⟨ sym-assoc ⟩
  ρ⇐ ∘ ((ρ⇒ ∘ σ⇒) ∘ λ⇐)
    ≈⟨ refl⟩∘⟨ (InvBraidedProperties.inv-braiding-coherence ⟩∘⟨refl) ⟩
  ρ⇐ ∘ (λ⇒ ∘ λ⇐)
    ≈⟨ refl⟩∘⟨ unitorˡ.isoʳ ⟩
  ρ⇐ ∘ id
    ≈⟨ identityʳ ⟩
  ρ⇐ ∎

-- `substₑ` of a reversed `cons`-congruence whiskers on the left.
substₑ-sym-cons : {b : Atom} {x y : List Atom} (p : x ≡ y)
  → substₑ (sym (cong (b ∷_) p)) ≈ id {⟦ b ⟧ₐ} ⊗₁ substₑ (sym p)
substₑ-sym-cons ≡refl = Equiv.sym ⊗.identity

-- Empty right merges collapse to the right unitor.
μ-nilʳ : (zs : List Atom)
  → μ zs [] ∘ substₑ (sym (++-identityʳ zs)) ≈ ρ⇐
μ-nilʳ [] = begin
  μ [] [] ∘ substₑ (sym (++-identityʳ []))
    ≈⟨ identityʳ ⟩
  λ⇐
    ≈⟨ coherence-inv₃ ⟩
  ρ⇐
    ∎
μ-nilʳ (z ∷ zs') = begin
  μ (z ∷ zs') [] ∘ substₑ (sym (++-identityʳ (z ∷ zs')))
    ≈⟨ refl⟩∘⟨ substₑ-sym-cons (++-identityʳ zs') ⟩
  (α⇐ ∘ (id ⊗₁ μ zs' [])) ∘ (id ⊗₁ substₑ (sym (++-identityʳ zs')))
    ≈⟨ assoc ⟩
  α⇐ ∘ ((id ⊗₁ μ zs' []) ∘ (id ⊗₁ substₑ (sym (++-identityʳ zs'))))
    ≈⟨ refl⟩∘⟨ (⟺ split₂ˡ) ⟩
  α⇐ ∘ (id ⊗₁ (μ zs' [] ∘ substₑ (sym (++-identityʳ zs'))))
    ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ μ-nilʳ zs' ⟩
  α⇐ ∘ (id ⊗₁ ρ⇐)
    ≈⟨ coherence-inv₂ ⟩
  ρ⇐ ∎

-- Braiding a block past another block, transported through `μ`.
block-swap : (xs ys : List Atom)
  → σ⇒ {⟦ xs ⟧ᴹ} {⟦ ys ⟧ᴹ} ∘ μ xs ys ≈ μ ys xs ∘ realize↭ (++-swap xs ys)
block-swap []        ys = begin
  σ⇒ ∘ μ [] ys
    ≈⟨ braid-unitˡ ⟩
  ρ⇐
    ≈˘⟨ μ-nilʳ ys ⟩
  μ ys [] ∘ substₑ (sym (++-identityʳ ys))
    ≈˘⟨ refl⟩∘⟨ realize↭-sym-reflexive (++-identityʳ ys) ⟩
  μ ys [] ∘ realize↭ (++-swap [] ys) ∎
block-swap (x ∷ xs') ys = begin
  σ⇒ ∘ μ (x ∷ xs') ys
    ≈⟨ pullˡ σ-hex₂ ⟩
  (swap₁ ⟦ x ⟧ₐ ⟦ ys ⟧ᴹ ⟦ xs' ⟧ᴹ ∘ (id ⊗₁ σ⇒ {⟦ xs' ⟧ᴹ} {⟦ ys ⟧ᴹ})) ∘ (id ⊗₁ μ xs' ys)
    ≈⟨ pullʳ (⟺ split₂ˡ) ⟩
  swap₁ ⟦ x ⟧ₐ ⟦ ys ⟧ᴹ ⟦ xs' ⟧ᴹ ∘ (id ⊗₁ (σ⇒ {⟦ xs' ⟧ᴹ} {⟦ ys ⟧ᴹ} ∘ μ xs' ys))
    ≈⟨ refl⟩∘⟨ refl⟩⊗⟨ block-swap xs' ys ⟩
  swap₁ ⟦ x ⟧ₐ ⟦ ys ⟧ᴹ ⟦ xs' ⟧ᴹ ∘ (id ⊗₁ (μ ys xs' ∘ realize↭ (++-swap xs' ys)))
    ≈⟨ refl⟩∘⟨ split₂ˡ ⟩
  swap₁ ⟦ x ⟧ₐ ⟦ ys ⟧ᴹ ⟦ xs' ⟧ᴹ ∘ ((id ⊗₁ μ ys xs') ∘ (id ⊗₁ realize↭ (++-swap xs' ys)))
    ≈⟨ pullˡ (braid-atom x ys xs') ⟩
  (μ ys (x ∷ xs') ∘ realize↭ (↭-sym (shift x ys xs'))) ∘ (id ⊗₁ realize↭ (++-swap xs' ys))
    ≈⟨ assoc ⟩
  -- `++-swap (x ∷ xs') ys` computes to the right factor.
  μ ys (x ∷ xs') ∘ (realize↭ (↭-sym (shift x ys xs')) ∘ (id ⊗₁ realize↭ (++-swap xs' ys))) ∎
  where
    -- Split block braiding into the leading atom and the suffix.
    σ-hex₂ : σ⇒ {⟦ x ∷ xs' ⟧ᴹ} {⟦ ys ⟧ᴹ} ∘ α⇐ {⟦ x ⟧ₐ} {⟦ xs' ⟧ᴹ} {⟦ ys ⟧ᴹ}
           ≈ swap₁ ⟦ x ⟧ₐ ⟦ ys ⟧ᴹ ⟦ xs' ⟧ᴹ ∘ (id ⊗₁ σ⇒ {⟦ xs' ⟧ᴹ} {⟦ ys ⟧ᴹ})
    -- `hexagon₂` unfolds to this plain `_≈_`.
    hex₂ : (α⇐ ∘ σ⇒ {⟦ x ⟧ₐ ⊗₀ ⟦ xs' ⟧ᴹ} {⟦ ys ⟧ᴹ}) ∘ α⇐
         ≈ (σ⇒ {⟦ x ⟧ₐ} {⟦ ys ⟧ᴹ} ⊗₁ id ∘ α⇐) ∘ (id ⊗₁ σ⇒ {⟦ xs' ⟧ᴹ} {⟦ ys ⟧ᴹ})
    hex₂ = ⟺ (hexagon₂ {X = ⟦ x ⟧ₐ} {Y = ⟦ xs' ⟧ᴹ} {Z = ⟦ ys ⟧ᴹ})

    σ-hex₂ = begin
      σ⇒ ∘ α⇐
        ≈˘⟨ Cancellers.cancelˡ (associator.isoʳ {⟦ ys ⟧ᴹ} {⟦ x ⟧ₐ} {⟦ xs' ⟧ᴹ}) ⟩
      α⇒ ∘ (α⇐ ∘ (σ⇒ ∘ α⇐))
        ≈⟨ refl⟩∘⟨ sym-assoc ⟩
      α⇒ ∘ ((α⇐ ∘ σ⇒) ∘ α⇐)
        ≈⟨ refl⟩∘⟨ hex₂ ⟩
      α⇒ ∘ ((σ⇒ {⟦ x ⟧ₐ} {⟦ ys ⟧ᴹ} ⊗₁ id ∘ α⇐) ∘ (id ⊗₁ σ⇒ {⟦ xs' ⟧ᴹ} {⟦ ys ⟧ᴹ}))
        ≈⟨ sym-assoc ⟩
      swap₁ ⟦ x ⟧ₐ ⟦ ys ⟧ᴹ ⟦ xs' ⟧ᴹ ∘ (id ⊗₁ σ⇒ {⟦ xs' ⟧ᴹ} {⟦ ys ⟧ᴹ}) ∎

-- Strictification soundness for the free braided category.
sound : ∀ {X Y} (f : X ⇒ᵇ Y)
  → ⟦ f ⟧ᵇ ∘ strict⁻¹ X ≈ strict⁻¹ Y ∘ realize↭ (⇒⇒perm f)
sound (idₘ {X})            = struct-sound (idᵐ {X})
sound (_∘ᵇ_ {X} {Y} {Z} g f)  = begin
  (⟦ g ⟧ᵇ ∘ ⟦ f ⟧ᵇ) ∘ strict⁻¹ X                             ≈⟨ assoc ⟩
  ⟦ g ⟧ᵇ ∘ (⟦ f ⟧ᵇ ∘ strict⁻¹ X)                             ≈⟨ refl⟩∘⟨ sound f ⟩
  ⟦ g ⟧ᵇ ∘ (strict⁻¹ Y ∘ realize↭ (⇒⇒perm f))                ≈⟨ pullˡ (sound g) ⟩
  (strict⁻¹ Z ∘ realize↭ (⇒⇒perm g)) ∘ realize↭ (⇒⇒perm f)   ≈⟨ assoc ⟩
  strict⁻¹ Z ∘ (realize↭ (⇒⇒perm g) ∘ realize↭ (⇒⇒perm f))   ∎
sound (α⇒ᵇ {X} {Y} {Z}) = struct-sound (α⇒ᵐ {X} {Y} {Z})
sound (α⇐ᵇ {X} {Y} {Z}) = struct-sound (α⇐ᵐ {X} {Y} {Z})
sound (λ⇒ᵇ {X})         = struct-sound (λ⇒ᵐ {X})
sound (λ⇐ᵇ {X})         = struct-sound (λ⇐ᵐ {X})
sound (ρ⇒ᵇ {X})         = struct-sound (ρ⇒ᵐ {X})
sound (ρ⇐ᵇ {X})         = struct-sound (ρ⇐ᵐ {X})
sound (_⊗ᵇ_ {X} {Y} {Z} {W} f g)  = begin
  (⟦ f ⟧ᵇ ⊗₁ ⟦ g ⟧ᵇ) ∘ ((strict⁻¹ X ⊗₁ strict⁻¹ Z) ∘ μ (nf X) (nf Z))
    ≈⟨ pullˡ (⟺ ⊗-distrib-over-∘) ⟩
  ((⟦ f ⟧ᵇ ∘ strict⁻¹ X) ⊗₁ (⟦ g ⟧ᵇ ∘ strict⁻¹ Z)) ∘ μ (nf X) (nf Z)
    ≈⟨ (sound f ⟩⊗⟨ sound g) ⟩∘⟨refl ⟩
  ((strict⁻¹ Y ∘ realize↭ (⇒⇒perm f)) ⊗₁ (strict⁻¹ W ∘ realize↭ (⇒⇒perm g))) ∘ μ (nf X) (nf Z)
    ≈⟨ ⊗-distrib-over-∘ ⟩∘⟨refl ⟩
  ((strict⁻¹ Y ⊗₁ strict⁻¹ W) ∘ (realize↭ (⇒⇒perm f) ⊗₁ realize↭ (⇒⇒perm g))) ∘ μ (nf X) (nf Z)
    ≈⟨ pullʳ (μ-realize (⇒⇒perm f) (⇒⇒perm g)) ⟩
  (strict⁻¹ Y ⊗₁ strict⁻¹ W) ∘ (μ (nf Y) (nf W) ∘ realize↭ (++⁺ (⇒⇒perm f) (⇒⇒perm g)))
    ≈⟨ sym-assoc ⟩
  ((strict⁻¹ Y ⊗₁ strict⁻¹ W) ∘ μ (nf Y) (nf W)) ∘ realize↭ (++⁺ (⇒⇒perm f) (⇒⇒perm g)) ∎
sound (β {X} {Y})  = begin
  σ⇒ ∘ ((strict⁻¹ X ⊗₁ strict⁻¹ Y) ∘ μ (nf X) (nf Y))
    ≈⟨ pullˡ (braiding.⇒.commute (strict⁻¹ X , strict⁻¹ Y)) ⟩
  ((strict⁻¹ Y ⊗₁ strict⁻¹ X) ∘ σ⇒ {⟦ nf X ⟧ᴹ} {⟦ nf Y ⟧ᴹ}) ∘ μ (nf X) (nf Y)
    ≈⟨ assoc ⟩
  (strict⁻¹ Y ⊗₁ strict⁻¹ X) ∘ (σ⇒ {⟦ nf X ⟧ᴹ} {⟦ nf Y ⟧ᴹ} ∘ μ (nf X) (nf Y))
    ≈⟨ refl⟩∘⟨ block-swap (nf X) (nf Y) ⟩
  (strict⁻¹ Y ⊗₁ strict⁻¹ X) ∘ (μ (nf Y) (nf X) ∘ realize↭ (++-swap (nf X) (nf Y)))
    ≈⟨ sym-assoc ⟩
  ((strict⁻¹ Y ⊗₁ strict⁻¹ X) ∘ μ (nf Y) (nf X)) ∘ realize↭ (++-swap (nf X) (nf Y)) ∎

-- Braided equality reduces to equality of realized permutations.
solve-realize : ∀ {X Y} (f g : X ⇒ᵇ Y)
  → realize↭ (⇒⇒perm f) ≈ realize↭ (⇒⇒perm g)
  → ⟦ f ⟧ᵇ ≈ ⟦ g ⟧ᵇ
solve-realize {X} {Y} f g eq = begin
  ⟦ f ⟧ᵇ
    ≈˘⟨ elimʳ strict-cancel ⟩
  ⟦ f ⟧ᵇ ∘ (strict⁻¹ X ∘ _≅_.from (strict X))
    ≈⟨ pullˡ (sound f) ⟩
  (strict⁻¹ Y ∘ realize↭ (⇒⇒perm f)) ∘ _≅_.from (strict X)
    ≈⟨ (refl⟩∘⟨ eq) ⟩∘⟨refl ⟩
  (strict⁻¹ Y ∘ realize↭ (⇒⇒perm g)) ∘ _≅_.from (strict X)
    ≈˘⟨ pullˡ (sound g) ⟩
  ⟦ g ⟧ᵇ ∘ (strict⁻¹ X ∘ _≅_.from (strict X))
    ≈⟨ elimʳ strict-cancel ⟩
  ⟦ g ⟧ᵇ ∎
  where
    strict-cancel : strict⁻¹ X ∘ _≅_.from (strict X) ≈ id
    strict-cancel = _≅_.isoˡ (strict X)
