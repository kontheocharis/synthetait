module LF.Base where

open import Agda.Primitive
open import Data.Product
open import Utils
open import Realignment

module In (S : Set) (Φ : S → Prop) where

  Setᵇ-iso : ∀ {ℓ s} → Φ s → Isomorph (Φ s → Set ℓ)
  Setᵇ-iso {ℓ} ϕ = record {
    [_] = Set ℓ ;
    iso = record {
        to = λ x → x ϕ ;
        from = λ x _ → x ;
        to-from = λ x → refl ;
        from-to = λ x → refl
      }
    }

  opaque
    Setᵇ : S → (ℓ : Level) → Set (lsuc ℓ)
    Setᵇ s ℓ = Realign (Φ s) (Φ s → Set ℓ) Setᵇ-iso

  opaque
    unfolding Setᵇ

    ⌞_⌟ᵇ : ∀ {ℓ s} → Set ℓ → Setᵇ s ℓ
    ⌞ A ⌟ᵇ = ⌞ (λ _ → A) ⌟

    Elᵇ : ∀ {ℓ s} → Setᵇ s ℓ → Set ℓ
    Elᵇ Aᵇ = (ϕ : Φ _) → ⌜ Aᵇ ⌝ ϕ

    private variable
      ℓ : Level
      s : S
      Aᵇ Bᵇ Cᵇ : Setᵇ s ℓ
      Fᵇ Gᵇ Hᵇ : Elᵇ Aᵇ → Setᵇ s ℓ
      aᵇ bᵇ cᵇ : Elᵇ Aᵇ
      fᵇ gᵇ hᵇ : (x : Elᵇ Aᵇ) → Elᵇ (Fᵇ x)

    Πᵇ : (Aᵇ : Setᵇ s ℓ) → (Elᵇ Aᵇ → Setᵇ s ℓ) → Setᵇ s ℓ
    Πᵇ Aᵇ Fᵇ = ⌞ ((x : Elᵇ Aᵇ) → Elᵇ (Fᵇ x)) ⌟ᵇ

    lamᵇ : ((x : Elᵇ Aᵇ) → Elᵇ (Fᵇ x)) → Elᵇ (Πᵇ Aᵇ Fᵇ)
    lamᵇ f = λ ϕ x _ → f x ϕ

    appᵇ : Elᵇ (Πᵇ Aᵇ Fᵇ) → (x : Elᵇ Aᵇ) → Elᵇ (Fᵇ x)
    appᵇ f = λ x ϕ → f ϕ x ϕ

    Πβᵇ : appᵇ (lamᵇ fᵇ) aᵇ ≡ fᵇ aᵇ
    Πβᵇ = refl

    Πηᵇ : {fᵇ : Elᵇ (Πᵇ Aᵇ Fᵇ)} → lamᵇ (appᵇ fᵇ) ≡ fᵇ
    Πηᵇ = refl

    {-# REWRITE Πβᵇ #-}
    {-# REWRITE Πηᵇ #-}

