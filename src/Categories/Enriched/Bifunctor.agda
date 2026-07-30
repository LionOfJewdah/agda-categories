{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)
open import Categories.Category.Monoidal.Core using (Monoidal)
open import Categories.Category.Monoidal.Symmetric using (Symmetric)

-- The two-action construction of an enriched bifunctor follows Kelly,
-- "Basic Concepts of Enriched Category Theory", Sections 1.5--1.6,
-- especially equation (1.21).

module Categories.Enriched.Bifunctor
  {o ℓ e} {V : Category o ℓ e} {M : Monoidal V} (S : Symmetric M) where

open import Data.Product using (_,_)

import Categories.Enriched.Category as Enriched

open Category V
open HomReasoning
open Monoidal M
open Symmetric S using (braided; commutative)
open import Categories.Category.Monoidal.Braided.Properties braided using (module Shorthands)
open import Categories.Category.Monoidal.Interchange.Braided braided
  renaming (hasInterchange to interchange)
open import Categories.Enriched.Action S public
  using ()
  renaming (CommutingActions to BifunctorHelper; module FromActions to FromHelper)
open import Categories.Enriched.Category.TensorProduct interchange using (_⊠_)
open import Categories.Enriched.Category.Opposite S renaming (op to opE)
open import Categories.Enriched.Functor M using (Functor; _∘F_)
open import Categories.Enriched.Functor.Opposite S using (opF)
open import Categories.Enriched.Functor.TensorProduct interchange using (_⊠F_)
open import Categories.Enriched.Functor.TensorProduct.Symmetric S
  using (op-⊠F; swapF; includeˡ; includeʳ)
open import Categories.Morphism.Reasoning V
open Shorthands

Bifunctor : ∀ {a b c} →
  Enriched.Category M a → Enriched.Category M b → Enriched.Category M c → Set _
Bifunctor 𝒜 ℬ 𝒞 = Functor (𝒜 ⊠ ℬ) 𝒞

op₂F : ∀ {a b c}
  {𝒜 : Enriched.Category M a} {ℬ : Enriched.Category M b}
  {𝒞 : Enriched.Category M c} →
  Bifunctor 𝒜 ℬ 𝒞 → Bifunctor (opE 𝒜) (opE ℬ) (opE 𝒞)
op₂F {𝒜 = 𝒜} {ℬ} {𝒞} H = record
  { map₀ = H′.₀
  ; map₁ = H′.₁
  ; identity = H′.identity
  ; homomorphism = op₂-homomorphism
  }
  where
  module 𝒜 = Enriched.Category 𝒜
  module ℬ = Enriched.Category ℬ
  module Source = Enriched.Category (opE 𝒜 ⊠ opE ℬ)
  module Middle = Enriched.Category (opE (𝒜 ⊠ ℬ))
  module Target = Enriched.Category (opE 𝒞)
  module H′ = Functor H
  module P = Functor (op-⊠F {𝒜 = 𝒜} {ℬ})
  module Q = Functor (opF H)

  abstract
    op₂-homomorphism : ∀ {A B C X Y Z} →
      H′.₁ {X = C , Z} {Y = A , X} ∘ Source.⊚ {A = A , X} {B , Y} {C , Z}
      ≈ Target.⊚ ∘ (H′.₁ ⊗₁ H′.₁)
    op₂-homomorphism = begin
      H′.₁ ∘ Source.⊚                           ≈˘⟨ refl⟩∘⟨ identityˡ ⟩
      H′.₁ ∘ (P.₁ ∘ Source.⊚)                   ≈⟨ pushʳ P.homomorphism ⟩
      (Q.₁ ∘ Middle.⊚) ∘ (P.₁ ⊗₁ P.₁)           ≈⟨ Q.homomorphism ⟩∘⟨refl ⟩
      (Target.⊚ ∘ (H′.₁ ⊗₁ H′.₁)) ∘ (id ⊗₁ id)  ≈⟨ elimʳ ⊗.identity ⟩
      Target.⊚ ∘ (H′.₁ ⊗₁ H′.₁)                 ∎

bifunctorHelper : ∀ {a b c}
  {𝒜 : Enriched.Category M a} {ℬ : Enriched.Category M b}
  {𝒞 : Enriched.Category M c} →
  BifunctorHelper 𝒜 ℬ 𝒞 → Bifunctor 𝒜 ℬ 𝒞
bifunctorHelper H = record
  { map₀ = λ (A , X) → BifunctorHelper.map₀ H A X
  ; map₁ = FromHelper.diagonal H
  ; identity = FromHelper.identity H
  ; homomorphism = FromHelper.homomorphism H
  }

module Helper {a b c}
  {𝒜 : Enriched.Category M a} {ℬ : Enriched.Category M b}
  {𝒞 : Enriched.Category M c} (H : BifunctorHelper 𝒜 ℬ 𝒞) where

  private
    module 𝒜 = Enriched.Category 𝒜
    module ℬ = Enriched.Category ℬ
    module 𝒞 = Enriched.Category 𝒞
    module H = BifunctorHelper H
    module Opˡ (A : 𝒜.Obj) = Functor (opF (FromHelper.appˡ H A))
    module Opʳ (B : ℬ.Obj) = Functor (opF (FromHelper.appʳ H B))

    abstract
      -- Push a functor through a composition-homomorphism.  Post-composing `F`
      -- after the action carries the homomorphism into `F`'s target; pre-composing
      -- `G` before it carries the source category's `⊚` in through `G`.
      push-postF : ∀ {d} {𝒟 : Enriched.Category M d} (F : Functor 𝒞 𝒟) →
        let module F = Functor F
            module 𝒟 = Enriched.Category 𝒟 in
        {Pˡ Pʳ Q : Obj} {Xa Xb Xc : 𝒞.Obj}
        {w : Pˡ ⊗₀ Pʳ ⇒ Q} {u : Q ⇒ 𝒞.hom Xa Xc}
        {uˡ : Pˡ ⇒ 𝒞.hom Xb Xc} {uʳ : Pʳ ⇒ 𝒞.hom Xa Xb} →
        u ∘ w ≈ 𝒞.⊚ ∘ (uˡ ⊗₁ uʳ) →
        (F.₁ ∘ u) ∘ w ≈ 𝒟.⊚ ∘ ((F.₁ ∘ uˡ) ⊗₁ (F.₁ ∘ uʳ))
      push-postF {𝒟 = 𝒟} F {w = w} {u} {uˡ} {uʳ} hom = begin
        (F.₁ ∘ u) ∘ w                      ≈⟨ pullʳ hom ⟩
        F.₁ ∘ 𝒞.⊚ ∘ (uˡ ⊗₁ uʳ)             ≈⟨ pullˡ F.homomorphism ⟩
        (𝒟.⊚ ∘ (F.₁ ⊗₁ F.₁)) ∘ (uˡ ⊗₁ uʳ)  ≈⟨ pullʳ (⟺ ⊗.homomorphism) ⟩
        𝒟.⊚ ∘ ((F.₁ ∘ uˡ) ⊗₁ (F.₁ ∘ uʳ))   ∎
        where module F = Functor F
              module 𝒟 = Enriched.Category 𝒟

      push-preF : ∀ {k k′} {𝒦 : Enriched.Category M k} {𝒦′ : Enriched.Category M k′}
        (G : Functor 𝒦′ 𝒦) →
        let module G = Functor G
            module 𝒦 = Enriched.Category 𝒦
            module 𝒦′ = Enriched.Category 𝒦′ in
        {A′ B′ C′ : 𝒦′.Obj} {Xa Xb Xc : 𝒞.Obj}
        {m : 𝒦.hom (G.₀ A′) (G.₀ C′) ⇒ 𝒞.hom Xa Xc}
        {mˡ : 𝒦.hom (G.₀ B′) (G.₀ C′) ⇒ 𝒞.hom Xb Xc}
        {mʳ : 𝒦.hom (G.₀ A′) (G.₀ B′) ⇒ 𝒞.hom Xa Xb} →
        m ∘ 𝒦.⊚ ≈ 𝒞.⊚ ∘ (mˡ ⊗₁ mʳ) →
        (m ∘ G.₁) ∘ 𝒦′.⊚ ≈ 𝒞.⊚ ∘ ((mˡ ∘ G.₁) ⊗₁ (mʳ ∘ G.₁))
      push-preF {𝒦 = 𝒦} {𝒦′} G {m = m} {mˡ} {mʳ} hom = begin
        (m ∘ G.₁) ∘ 𝒦′.⊚                   ≈⟨ pullʳ G.homomorphism ⟩
        m ∘ 𝒦.⊚ ∘ (G.₁ ⊗₁ G.₁)             ≈⟨ pullˡ hom ⟩
        (𝒞.⊚ ∘ (mˡ ⊗₁ mʳ)) ∘ (G.₁ ⊗₁ G.₁)  ≈⟨ pullʳ (⟺ ⊗.homomorphism) ⟩
        𝒞.⊚ ∘ ((mˡ ∘ G.₁) ⊗₁ (mʳ ∘ G.₁))   ∎
        where module G = Functor G
              module 𝒦 = Enriched.Category 𝒦
              module 𝒦′ = Enriched.Category 𝒦′

      commute-flipped : (A B : 𝒜.Obj) (X Y : ℬ.Obj) →
        𝒞.⊚ ∘ (H.mapʳ B X Y ⊗₁ H.mapˡ A B X)
        ≈ (𝒞.⊚ ∘ (H.mapˡ A B Y ⊗₁ H.mapʳ A X Y)) ∘ σ⇒
      commute-flipped A B X Y = begin
        𝒞.⊚ ∘ (H.mapʳ B X Y ⊗₁ H.mapˡ A B X)                ≈⟨ introʳ commutative ⟩
        (𝒞.⊚ ∘ (H.mapʳ B X Y ⊗₁ H.mapˡ A B X)) ∘ σ⇒ ∘ σ⇒    ≈˘⟨ assoc ⟩
        ((𝒞.⊚ ∘ (H.mapʳ B X Y ⊗₁ H.mapˡ A B X)) ∘ σ⇒) ∘ σ⇒  ≈˘⟨ H.commute A B X Y ⟩∘⟨refl ⟩
        (𝒞.⊚ ∘ (H.mapˡ A B Y ⊗₁ H.mapʳ A X Y)) ∘ σ⇒         ∎

  postcompose : ∀ {d} {𝒟 : Enriched.Category M d} →
    Functor 𝒞 𝒟 → BifunctorHelper 𝒜 ℬ 𝒟
  postcompose {𝒟 = 𝒟} F = record
    { map₀ = λ A B → F′.₀ (H.map₀ A B)
    ; mapˡ = λ A B X → F′.₁ ∘ H.mapˡ A B X
    ; mapʳ = λ A X Y → F′.₁ ∘ H.mapʳ A X Y
    ; identityˡ = λ A X → pullʳ (H.identityˡ A X) ○ F′.identity
    ; identityʳ = λ A X → pullʳ (H.identityʳ A X) ○ F′.identity
    ; homomorphismˡ = λ A B C X → push-postF F (H.homomorphismˡ A B C X)
    ; homomorphismʳ = λ A X Y Z → push-postF F (H.homomorphismʳ A X Y Z)
    ; commute = λ A B X Y → begin
        𝒟.⊚ ∘ ((F′.₁ ∘ H.mapˡ A B Y) ⊗₁ (F′.₁ ∘ H.mapʳ A X Y))
          ≈⟨ refl⟩∘⟨ ⊗.homomorphism ⟩
        𝒟.⊚ ∘ ((F′.₁ ⊗₁ F′.₁) ∘ (H.mapˡ A B Y ⊗₁ H.mapʳ A X Y))
          ≈˘⟨ assoc ⟩
        (𝒟.⊚ ∘ (F′.₁ ⊗₁ F′.₁)) ∘ (H.mapˡ A B Y ⊗₁ H.mapʳ A X Y)
          ≈˘⟨ F′.homomorphism ⟩∘⟨refl ⟩
        (F′.₁ ∘ 𝒞.⊚) ∘ (H.mapˡ A B Y ⊗₁ H.mapʳ A X Y)
          ≈⟨ pullʳ (H.commute A B X Y) ⟩
        F′.₁ ∘ (𝒞.⊚ ∘ (H.mapʳ B X Y ⊗₁ H.mapˡ A B X)) ∘ σ⇒
          ≈˘⟨ assoc ⟩
        (F′.₁ ∘ (𝒞.⊚ ∘ (H.mapʳ B X Y ⊗₁ H.mapˡ A B X))) ∘ σ⇒
          ≈⟨ pullˡ F′.homomorphism ⟩∘⟨refl ⟩
        ((𝒟.⊚ ∘ (F′.₁ ⊗₁ F′.₁)) ∘ (H.mapʳ B X Y ⊗₁ H.mapˡ A B X)) ∘ σ⇒
          ≈⟨ assoc ⟩∘⟨refl ⟩
        (𝒟.⊚ ∘ ((F′.₁ ⊗₁ F′.₁) ∘ (H.mapʳ B X Y ⊗₁ H.mapˡ A B X))) ∘ σ⇒
          ≈˘⟨ (refl⟩∘⟨ ⊗.homomorphism) ⟩∘⟨refl ⟩
        (𝒟.⊚ ∘ ((F′.₁ ∘ H.mapʳ B X Y) ⊗₁ (F′.₁ ∘ H.mapˡ A B X))) ∘ σ⇒ ∎
    }
    where
    module 𝒟 = Enriched.Category 𝒟
    module F′ = Functor F

  reduce : ∀ {a′ b′}
    {𝒜′ : Enriched.Category M a′} {ℬ′ : Enriched.Category M b′} →
    Functor 𝒜′ 𝒜 → Functor ℬ′ ℬ → BifunctorHelper 𝒜′ ℬ′ 𝒞
  reduce {𝒜′ = 𝒜′} {ℬ′} F G = record
    { map₀ = λ A B → H.map₀ (F′.₀ A) (G′.₀ B)
    ; mapˡ = λ A B X → H.mapˡ (F′.₀ A) (F′.₀ B) (G′.₀ X) ∘ F′.₁
    ; mapʳ = λ A X Y → H.mapʳ (F′.₀ A) (G′.₀ X) (G′.₀ Y) ∘ G′.₁
    ; identityˡ = λ A X → pullʳ F′.identity ○ H.identityˡ (F′.₀ A) (G′.₀ X)
    ; identityʳ = λ A X → pullʳ G′.identity ○ H.identityʳ (F′.₀ A) (G′.₀ X)
    ; homomorphismˡ = λ A B C X →
        push-preF F (H.homomorphismˡ (F′.₀ A) (F′.₀ B) (F′.₀ C) (G′.₀ X))
    ; homomorphismʳ = λ A X Y Z →
        push-preF G (H.homomorphismʳ (F′.₀ A) (G′.₀ X) (G′.₀ Y) (G′.₀ Z))
    ; commute = λ A B X Y → begin
        𝒞.⊚ ∘
          ((H.mapˡ (F′.₀ A) (F′.₀ B) (G′.₀ Y) ∘ F′.₁) ⊗₁
           (H.mapʳ (F′.₀ A) (G′.₀ X) (G′.₀ Y) ∘ G′.₁))
          ≈⟨ refl⟩∘⟨ ⊗.homomorphism ⟩
        𝒞.⊚ ∘
          (H.mapˡ (F′.₀ A) (F′.₀ B) (G′.₀ Y) ⊗₁
           H.mapʳ (F′.₀ A) (G′.₀ X) (G′.₀ Y)) ∘ (F′.₁ ⊗₁ G′.₁)
          ≈⟨ pullˡ (H.commute (F′.₀ A) (F′.₀ B) (G′.₀ X) (G′.₀ Y)) ⟩
        ((𝒞.⊚ ∘
          (H.mapʳ (F′.₀ B) (G′.₀ X) (G′.₀ Y) ⊗₁
           H.mapˡ (F′.₀ A) (F′.₀ B) (G′.₀ X))) ∘ σ⇒) ∘ (F′.₁ ⊗₁ G′.₁)
          ≈⟨ pullʳ σ⇒-comm ⟩
        (𝒞.⊚ ∘
          (H.mapʳ (F′.₀ B) (G′.₀ X) (G′.₀ Y) ⊗₁
           H.mapˡ (F′.₀ A) (F′.₀ B) (G′.₀ X))) ∘ (G′.₁ ⊗₁ F′.₁) ∘ σ⇒
          ≈˘⟨ assoc ⟩
        ((𝒞.⊚ ∘
          (H.mapʳ (F′.₀ B) (G′.₀ X) (G′.₀ Y) ⊗₁
           H.mapˡ (F′.₀ A) (F′.₀ B) (G′.₀ X))) ∘ (G′.₁ ⊗₁ F′.₁)) ∘ σ⇒
          ≈⟨ assoc ⟩∘⟨refl ⟩
        (𝒞.⊚ ∘
          ((H.mapʳ (F′.₀ B) (G′.₀ X) (G′.₀ Y) ⊗₁
            H.mapˡ (F′.₀ A) (F′.₀ B) (G′.₀ X)) ∘ (G′.₁ ⊗₁ F′.₁))) ∘ σ⇒
          ≈˘⟨ (refl⟩∘⟨ ⊗.homomorphism) ⟩∘⟨refl ⟩
        (𝒞.⊚ ∘
          ((H.mapʳ (F′.₀ B) (G′.₀ X) (G′.₀ Y) ∘ G′.₁) ⊗₁
           (H.mapˡ (F′.₀ A) (F′.₀ B) (G′.₀ X) ∘ F′.₁))) ∘ σ⇒ ∎
    }
    where
    module 𝒜′ = Enriched.Category 𝒜′
    module ℬ′ = Enriched.Category ℬ′
    module F′ = Functor F
    module G′ = Functor G

  reduce-flipped : ∀ {a′ b′}
    {𝒜′ : Enriched.Category M a′} {ℬ′ : Enriched.Category M b′} →
    Functor 𝒜′ ℬ → Functor ℬ′ 𝒜 → BifunctorHelper 𝒜′ ℬ′ 𝒞
  reduce-flipped {𝒜′ = 𝒜′} {ℬ′} F G = record
    { map₀ = λ A B → H.map₀ (G′.₀ B) (F′.₀ A)
    ; mapˡ = λ A B X → H.mapʳ (G′.₀ X) (F′.₀ A) (F′.₀ B) ∘ F′.₁
    ; mapʳ = λ A X Y → H.mapˡ (G′.₀ X) (G′.₀ Y) (F′.₀ A) ∘ G′.₁
    ; identityˡ = reduce-idˡ
    ; identityʳ = reduce-idʳ
    ; homomorphismˡ = reduce-∘ˡ
    ; homomorphismʳ = reduce-∘ʳ
    ; commute = reduce-commute
    }
    where
    module 𝒜′ = Enriched.Category 𝒜′
    module ℬ′ = Enriched.Category ℬ′
    module F′ = Functor F
    module G′ = Functor G

    variable
      A B C : 𝒜′.Obj
      X Y Z : ℬ′.Obj

    abstract
        reduce-idˡ : (A : 𝒜′.Obj) (X : ℬ′.Obj) →
          (H.mapʳ (G′.₀ X) (F′.₀ A) (F′.₀ A) ∘ F′.₁) ∘ 𝒜′.id ≈ 𝒞.id
        reduce-idˡ A X = pullʳ F′.identity ○ H.identityʳ (G′.₀ X) (F′.₀ A)

        reduce-idʳ : (A : 𝒜′.Obj) (X : ℬ′.Obj) →
          (H.mapˡ (G′.₀ X) (G′.₀ X) (F′.₀ A) ∘ G′.₁) ∘ ℬ′.id ≈ 𝒞.id
        reduce-idʳ A X = pullʳ G′.identity ○ H.identityˡ (G′.₀ X) (F′.₀ A)

        reduce-∘ˡ : (A B C : 𝒜′.Obj) (X : ℬ′.Obj) →
          (H.mapʳ (G′.₀ X) (F′.₀ A) (F′.₀ C) ∘ F′.₁) ∘ 𝒜′.⊚
          ≈ 𝒞.⊚ ∘
            ((H.mapʳ (G′.₀ X) (F′.₀ B) (F′.₀ C) ∘ F′.₁) ⊗₁
             (H.mapʳ (G′.₀ X) (F′.₀ A) (F′.₀ B) ∘ F′.₁))
        reduce-∘ˡ A B C X =
          push-preF F (H.homomorphismʳ (G′.₀ X) (F′.₀ A) (F′.₀ B) (F′.₀ C))

        reduce-∘ʳ : (A : 𝒜′.Obj) (X Y Z : ℬ′.Obj) →
          (H.mapˡ (G′.₀ X) (G′.₀ Z) (F′.₀ A) ∘ G′.₁) ∘ ℬ′.⊚
          ≈ 𝒞.⊚ ∘
            ((H.mapˡ (G′.₀ Y) (G′.₀ Z) (F′.₀ A) ∘ G′.₁) ⊗₁
             (H.mapˡ (G′.₀ X) (G′.₀ Y) (F′.₀ A) ∘ G′.₁))
        reduce-∘ʳ A X Y Z =
          push-preF G (H.homomorphismˡ (G′.₀ X) (G′.₀ Y) (G′.₀ Z) (F′.₀ A))

        reduce-commute : (A B : 𝒜′.Obj) (X Y : ℬ′.Obj) →
          𝒞.⊚ ∘
            ((H.mapʳ (G′.₀ Y) (F′.₀ A) (F′.₀ B) ∘ F′.₁) ⊗₁
             (H.mapˡ (G′.₀ X) (G′.₀ Y) (F′.₀ A) ∘ G′.₁))
          ≈ (𝒞.⊚ ∘
            ((H.mapˡ (G′.₀ X) (G′.₀ Y) (F′.₀ B) ∘ G′.₁) ⊗₁
             (H.mapʳ (G′.₀ X) (F′.₀ A) (F′.₀ B) ∘ F′.₁))) ∘ σ⇒
        reduce-commute A B X Y = begin
          𝒞.⊚ ∘
            ((H.mapʳ (G′.₀ Y) (F′.₀ A) (F′.₀ B) ∘ F′.₁) ⊗₁
             (H.mapˡ (G′.₀ X) (G′.₀ Y) (F′.₀ A) ∘ G′.₁))
            ≈⟨ refl⟩∘⟨ ⊗.homomorphism ⟩
          𝒞.⊚ ∘
            (H.mapʳ (G′.₀ Y) (F′.₀ A) (F′.₀ B) ⊗₁
             H.mapˡ (G′.₀ X) (G′.₀ Y) (F′.₀ A)) ∘ (F′.₁ ⊗₁ G′.₁)
            ≈⟨ pullˡ (commute-flipped (G′.₀ X) (G′.₀ Y) (F′.₀ A) (F′.₀ B)) ⟩
          ((𝒞.⊚ ∘
            (H.mapˡ (G′.₀ X) (G′.₀ Y) (F′.₀ B) ⊗₁
             H.mapʳ (G′.₀ X) (F′.₀ A) (F′.₀ B))) ∘ σ⇒) ∘ (F′.₁ ⊗₁ G′.₁)
            ≈⟨ pullʳ σ⇒-comm ⟩
          (𝒞.⊚ ∘
            (H.mapˡ (G′.₀ X) (G′.₀ Y) (F′.₀ B) ⊗₁
             H.mapʳ (G′.₀ X) (F′.₀ A) (F′.₀ B))) ∘ (G′.₁ ⊗₁ F′.₁) ∘ σ⇒
            ≈˘⟨ assoc ⟩
          ((𝒞.⊚ ∘
            (H.mapˡ (G′.₀ X) (G′.₀ Y) (F′.₀ B) ⊗₁
             H.mapʳ (G′.₀ X) (F′.₀ A) (F′.₀ B))) ∘ (G′.₁ ⊗₁ F′.₁)) ∘ σ⇒
            ≈⟨ assoc ⟩∘⟨refl ⟩
          (𝒞.⊚ ∘
            ((H.mapˡ (G′.₀ X) (G′.₀ Y) (F′.₀ B) ⊗₁
              H.mapʳ (G′.₀ X) (F′.₀ A) (F′.₀ B)) ∘ (G′.₁ ⊗₁ F′.₁))) ∘ σ⇒
          ≈˘⟨ (refl⟩∘⟨ ⊗.homomorphism) ⟩∘⟨refl ⟩
          (𝒞.⊚ ∘
            ((H.mapˡ (G′.₀ X) (G′.₀ Y) (F′.₀ B) ∘ G′.₁) ⊗₁
             (H.mapʳ (G′.₀ X) (F′.₀ A) (F′.₀ B) ∘ F′.₁))) ∘ σ⇒ ∎

  abstract
    reduce-flipped-diagonal : ∀ {a′ b′}
      {𝒜′ : Enriched.Category M a′} {ℬ′ : Enriched.Category M b′}
      (F : Functor 𝒜′ ℬ) (G : Functor ℬ′ 𝒜)
      {A B : Enriched.Category.Obj 𝒜′} {X Y : Enriched.Category.Obj ℬ′} →
      FromHelper.diagonal (reduce-flipped F G) {A₁ = A} {A₂ = B} {B₁ = X} {B₂ = Y}
      ≈ Functor.₁ (bifunctorHelper H ∘F (G ⊠F F) ∘F swapF)
    reduce-flipped-diagonal F G = begin
      FromHelper.diagonal (reduce-flipped F G)
        ≈⟨ refl⟩∘⟨ ⊗.homomorphism ⟩
      𝒞.⊚ ∘ (H.mapʳ _ _ _ ⊗₁ H.mapˡ _ _ _) ∘ (F′.₁ ⊗₁ G′.₁)
        ≈⟨ pullˡ (commute-flipped _ _ _ _) ⟩
      ((𝒞.⊚ ∘ (H.mapˡ _ _ _ ⊗₁ H.mapʳ _ _ _)) ∘ σ⇒) ∘ (F′.₁ ⊗₁ G′.₁)
        ≈⟨ pullʳ σ⇒-comm ⟩
      (𝒞.⊚ ∘ (H.mapˡ _ _ _ ⊗₁ H.mapʳ _ _ _)) ∘ (G′.₁ ⊗₁ F′.₁) ∘ σ⇒
        ∎
      where
      module F′ = Functor F
      module G′ = Functor G

  flip : BifunctorHelper ℬ 𝒜 𝒞
  flip = record
    { map₀ = λ B A → H.map₀ A B
    ; mapˡ = λ A B X → H.mapʳ X A B
    ; mapʳ = λ A X Y → H.mapˡ X Y A
    ; identityˡ = λ A X → H.identityʳ X A
    ; identityʳ = λ A X → H.identityˡ X A
    ; homomorphismˡ = λ A B C X → H.homomorphismʳ X A B C
    ; homomorphismʳ = λ A X Y Z → H.homomorphismˡ X Y Z A
    ; commute = λ A B X Y → commute-flipped X Y A B
    }

  private abstract
    op-commute : (A B : 𝒜.Obj) (X Y : ℬ.Obj) →
      (𝒞.⊚ ∘ σ⇒) ∘ (H.mapˡ B A Y ⊗₁ H.mapʳ A Y X)
      ≈ (((𝒞.⊚ ∘ σ⇒) ∘ (H.mapʳ B Y X ⊗₁ H.mapˡ B A X)) ∘ σ⇒)
    op-commute A B X Y = begin
      (𝒞.⊚ ∘ σ⇒) ∘ (H.mapˡ B A Y ⊗₁ H.mapʳ A Y X)
        ≈⟨ extendˡ σ⇒-comm ⟩
      (𝒞.⊚ ∘ (H.mapʳ A Y X ⊗₁ H.mapˡ B A Y)) ∘ σ⇒
        ≈˘⟨ H.commute B A Y X ⟩
      𝒞.⊚ ∘ (H.mapˡ B A X ⊗₁ H.mapʳ B Y X)
        ≈˘⟨ cancelʳ commutative ⟩
      ((𝒞.⊚ ∘ (H.mapˡ B A X ⊗₁ H.mapʳ B Y X)) ∘ σ⇒) ∘ σ⇒
        ≈˘⟨ extendˡ σ⇒-comm ⟩∘⟨refl ⟩
      ((𝒞.⊚ ∘ σ⇒) ∘ (H.mapʳ B Y X ⊗₁ H.mapˡ B A X)) ∘ σ⇒ ∎

  op₂ : BifunctorHelper (opE 𝒜) (opE ℬ) (opE 𝒞)
  op₂ = record
    { map₀ = H.map₀
    ; mapˡ = λ A B X → Opʳ.₁ X
    ; mapʳ = λ A X Y → Opˡ.₁ A
    ; identityˡ = λ A X → Opʳ.identity X
    ; identityʳ = λ A X → Opˡ.identity A
    ; homomorphismˡ = λ A B C X → Opʳ.homomorphism X
    ; homomorphismʳ = λ A X Y Z → Opˡ.homomorphism A
    ; commute = op-commute
    }

  abstract
    op₂-diagonal : (A B : 𝒜.Obj) (X Y : ℬ.Obj) →
      FromHelper.diagonal op₂ {A₁ = A} {A₂ = B} {B₁ = X} {B₂ = Y}
      ≈ FromHelper.diagonal H
    op₂-diagonal A B X Y = begin
      (𝒞.⊚ ∘ σ⇒) ∘ (H.mapˡ B A Y ⊗₁ H.mapʳ A Y X)
        ≈⟨ extendˡ σ⇒-comm ⟩
      (𝒞.⊚ ∘ (H.mapʳ A Y X ⊗₁ H.mapˡ B A Y)) ∘ σ⇒
        ≈˘⟨ H.commute B A Y X ⟩
      𝒞.⊚ ∘ (H.mapˡ B A X ⊗₁ H.mapʳ B Y X) ∎

postcompose-helper : ∀ {a b c d}
  {𝒜 : Enriched.Category M a} {ℬ : Enriched.Category M b}
  {𝒞 : Enriched.Category M c} {𝒟 : Enriched.Category M d} →
  Functor 𝒞 𝒟 → BifunctorHelper 𝒜 ℬ 𝒞 → BifunctorHelper 𝒜 ℬ 𝒟
postcompose-helper F H = Helper.postcompose H F

module Postcomposition {a b c}
  {𝒜 : Enriched.Category M a} {ℬ : Enriched.Category M b}
  {𝒞 : Enriched.Category M c} {H : BifunctorHelper 𝒜 ℬ 𝒞} where

  private
    module 𝒜 = Enriched.Category 𝒜
    module ℬ = Enriched.Category ℬ

    variable
      A B : 𝒜.Obj
      X Y : ℬ.Obj

  abstract
    diagonal : ∀ {d} {𝒟 : Enriched.Category M d} (F : Functor 𝒞 𝒟) →
      FromHelper.diagonal (postcompose-helper F H) {A₁ = A} {A₂ = B} {B₁ = X} {B₂ = Y}
      ≈ Functor.₁ F ∘ FromHelper.diagonal H
    diagonal F =
      (refl⟩∘⟨ ⊗.homomorphism) ○ pullˡ (⟺ (Functor.homomorphism F)) ○ assoc

reduce-helper : ∀ {a b c a′ b′}
  {𝒜 : Enriched.Category M a} {ℬ : Enriched.Category M b}
  {𝒞 : Enriched.Category M c} {𝒜′ : Enriched.Category M a′}
  {ℬ′ : Enriched.Category M b′} →
  BifunctorHelper 𝒜 ℬ 𝒞 → Functor 𝒜′ 𝒜 → Functor ℬ′ ℬ →
  BifunctorHelper 𝒜′ ℬ′ 𝒞
reduce-helper H = Helper.reduce H

reduce-flipped-helper : ∀ {a b c a′ b′}
  {𝒜 : Enriched.Category M a} {ℬ : Enriched.Category M b}
  {𝒞 : Enriched.Category M c} {𝒜′ : Enriched.Category M a′}
  {ℬ′ : Enriched.Category M b′} →
  BifunctorHelper 𝒜 ℬ 𝒞 → Functor 𝒜′ ℬ → Functor ℬ′ 𝒜 →
  BifunctorHelper 𝒜′ ℬ′ 𝒞
reduce-flipped-helper H = Helper.reduce-flipped H

flip-helper : ∀ {a b c}
  {𝒜 : Enriched.Category M a} {ℬ : Enriched.Category M b}
  {𝒞 : Enriched.Category M c} →
  BifunctorHelper 𝒜 ℬ 𝒞 → BifunctorHelper ℬ 𝒜 𝒞
flip-helper = Helper.flip

op₂-helper : ∀ {a b c}
  {𝒜 : Enriched.Category M a} {ℬ : Enriched.Category M b}
  {𝒞 : Enriched.Category M c} →
  BifunctorHelper 𝒜 ℬ 𝒞 → BifunctorHelper (opE 𝒜) (opE ℬ) (opE 𝒞)
op₂-helper = Helper.op₂

module Bifunctor {a b c}
  {𝒜 : Enriched.Category M a} {ℬ : Enriched.Category M b}
  {𝒞 : Enriched.Category M c} (H : Bifunctor 𝒜 ℬ 𝒞) where

  private
    module 𝒜 = Enriched.Category 𝒜
    module ℬ = Enriched.Category ℬ

  open Functor H public

  reduce-⊠ : ∀ {a′ b′}
    {𝒜′ : Enriched.Category M a′} {ℬ′ : Enriched.Category M b′} →
    Functor 𝒜′ 𝒜 → Functor ℬ′ ℬ → Bifunctor 𝒜′ ℬ′ 𝒞
  reduce-⊠ F G = H ∘F (F ⊠F G)

  appˡ : 𝒜.Obj → Functor ℬ 𝒞
  appˡ A = H ∘F includeˡ 𝒜 ℬ A

  appʳ : ℬ.Obj → Functor 𝒜 𝒞
  appʳ B = H ∘F includeʳ 𝒜 ℬ B

open Bifunctor public using (reduce-⊠; appˡ; appʳ)
