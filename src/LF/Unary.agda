module LF.Unary where

open import Agda.Primitive
open import Data.Product
open import Data.Unit using (tt) renaming (⊤ to 𝟙)
open import Utils renaming (tt to ttᴾ)
open import Realignment
open import LF.Base
open import Level

module Unary (ϕ : Prop) where
  open LF.Base.In 𝟙 (λ _ → ϕ) public

  variable
    ℓ : Level
    Aᵇ Bᵇ : Setᵇ tt ℓ
    Fᵇ Gᵇ : Elᵇ Aᵇ → Setᵇ tt ℓ
    aᵇ bᵇ : Elᵇ Aᵇ
    fᵇ : (x : Elᵇ Aᵇ) → Elᵇ (Fᵇ x)

  opaque
    Setᶠ-𝟙 : (ℓ : Level) → Set (lsuc ℓ)
    Setᶠ-𝟙 ℓ = Σ[ X ∈ Set ℓ ] (ϕ → (X ≡ Lift ℓ 𝟙) true)

    Setᶠ : Setᵇ tt ℓ → Set (lsuc ℓ)
    Setᶠ {ℓ} Aᵇ = Elᵇ Aᵇ → Setᶠ-𝟙 ℓ

  opaque
    unfolding Setᶠ

    Elᶠ : ∀ {Aᵇ : Setᵇ tt ℓ} → Setᶠ Aᵇ → Elᵇ Aᵇ → Set ℓ
    Elᶠ Aᶠ aᵇ = Aᶠ aᵇ .proj₁

    variable
      Aᶠ Bᶠ : Setᶠ Aᵇ
      Fᶠ Gᶠ : ∀ {aᵇ} → Elᶠ Aᶠ aᵇ → Setᶠ (Fᵇ aᵇ)

    contr : ∀ {ℓ} {A : Set ℓ} → ((A ≡ Lift ℓ 𝟙) true) → (x y : A) → x ≡ y
    contr (by refl) x y = refl

    Πᶠ : (Aᶠ : Setᶠ Aᵇ) → (∀ {aᵇ} → Elᶠ Aᶠ aᵇ → Setᶠ (Fᵇ aᵇ)) → Setᶠ (Πᵇ Aᵇ Fᵇ)
    Πᶠ {Aᵇ = Aᵇ} {Fᵇ = Fᵇ} Aᶠ Fᶠ f =
        Realign ϕ (∀ {aᵇ} (aᶠ : Elᶠ Aᶠ aᵇ) → Elᶠ (Fᶠ aᶠ) (appᵇ f aᵇ)) (λ p →
          record {
            [_] = Lift _ 𝟙 ;
            iso = record {
              to = λ _ → lift tt ;
              from = λ _ {aᵇ} aᶠ →
                coe (sym (Fᶠ aᶠ (appᵇ f aᵇ) .proj₂ p .witness)) (lift tt) ;
              to-from = λ _ → refl ;
              from-to = λ g → ifunext λ aᵇ → funext λ aᶠ →
                  contr (Fᶠ aᶠ (appᵇ f aᵇ) .proj₂ p) _ (g aᶠ)
            }
          }),
          λ p → by (ϕ→Realign p)
