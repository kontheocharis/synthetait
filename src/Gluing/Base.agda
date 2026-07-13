module Gluing.Base where

open import Agda.Primitive
open import Utils
open import Data.Product
open import Data.Unit using () renaming (⊤ to 𝟙; tt to tt𝟙)
open import Data.Bool using (Bool)
open import Level using (Lift; lift)
open import Gluing.Realignment

module In (ϕ : Prop) where
  private variable
    ℓ ℓ' : Level

  private
    Setᵇ-iso : ϕ → Isomorph (ϕ → Set ℓ)
    Setᵇ-iso {ℓ = ℓ} p = record
      { [_] = Set ℓ
      ; iso = record
          { to = λ f → f p
          ; from = λ X _ → X
          ; to-from = λ _ → refl
          ; from-to = λ _ → refl
          }
      }

  -- Base universe
  -- This is the realigned version of ϕ → Set

  opaque
    Setᵇ : (ℓ : Level) → Set (lsuc ℓ)
    Setᵇ ℓ = Realign ϕ (ϕ → Set ℓ) Setᵇ-iso

    Elᵇ-iso : (Aᵇ : Realign ϕ (ϕ → Set ℓ) Setᵇ-iso)
      → ϕ → Isomorph ((p : ϕ) → ⌜ Aᵇ ⌝ᴿ p)
    Elᵇ-iso Aᵇ p = record
      { [_] = ⌜ Aᵇ ⌝ᴿ p
      ; iso = record
          { to = λ f → f p
          ; from = λ x _ → x
          ; to-from = λ _ → refl
          ; from-to = λ _ → refl
          }
      }

    Elᵇ : Setᵇ ℓ → Set ℓ
    Elᵇ Aᵇ = Realign ϕ ((p : ϕ) → ⌜ Aᵇ ⌝ᴿ p) (Elᵇ-iso Aᵇ)

  private variable
    Aᵇ Bᵇ Cᵇ : Setᵇ ℓ
    Fᵇ Gᵇ : Elᵇ Aᵇ → Setᵇ ℓ
    aᵇ bᵇ cᵇ : Elᵇ Aᵇ
    fᵇ gᵇ : (x : Elᵇ Aᵇ) → Elᵇ (Fᵇ x)
    A : Set ℓ
    A' B' : ϕ → Set ℓ
    f g : (p : ϕ) → A' p


  -- Wrap/unwrap
  opaque
    unfolding Setᵇ Elᵇ

    ⌞_⌟ᵇ : (ϕ → Set ℓ) → Setᵇ ℓ
    ⌞ A ⌟ᵇ = ⌞ A ⌟ᴿ

    ⌜_⌝ᵇ : Setᵇ ℓ → (ϕ → Set ℓ)
    ⌜ Aᵇ ⌝ᵇ = ⌜ Aᵇ ⌝ᴿ

    ⌜⌞⌟⌝ᵇ' : ∀ {A' : ϕ → Set ℓ} → ⌜ ⌞ A' ⌟ᵇ ⌝ᵇ ≡ A'
    ⌜⌞⌟⌝ᵇ' = refl

    ⌞⌜⌝⌟ᵇ' : ∀ {Aᵇ : Setᵇ ℓ} → ⌞ ⌜ Aᵇ ⌝ᵇ ⌟ᵇ ≡ Aᵇ
    ⌞⌜⌝⌟ᵇ' = refl

    ⌞_⌟ : ((p : ϕ) → ⌜ Aᵇ ⌝ᵇ p) → Elᵇ Aᵇ
    ⌞ f ⌟ = ⌞ f ⌟ᴿ

    ⌜_⌝ : Elᵇ Aᵇ → (p : ϕ) → ⌜ Aᵇ ⌝ᵇ p
    ⌜ a ⌝ = ⌜ a ⌝ᴿ

    ⌜⌞⌟⌝ᵇ : ⌜ ⌞ f ⌟ ⌝ ≡ f
    ⌜⌞⌟⌝ᵇ = refl

    ⌞⌜⌝⌟ᵇ : ⌞ ⌜ aᵇ ⌝ ⌟ ≡ aᵇ
    ⌞⌜⌝⌟ᵇ = refl

  {-# REWRITE ⌜⌞⌟⌝ᵇ' ⌞⌜⌝⌟ᵇ' #-}
  {-# REWRITE ⌜⌞⌟⌝ᵇ ⌞⌜⌝⌟ᵇ #-}

  inj-⌞⌟ᵇ' : ⌞ A' ⌟ᵇ ≡ ⌞ B' ⌟ᵇ → A' ≡ B'
  inj-⌞⌟ᵇ' p = cong ⌜_⌝ᵇ p

  inj-⌞⌟ᵇ : ⌞ f ⌟ ≡ ⌞ g ⌟ → f ≡ g
  inj-⌞⌟ᵇ p = cong ⌜_⌝ p

  inj-⌜⌝ᵇ : ⌜ aᵇ ⌝ ≡ ⌜ bᵇ ⌝ → aᵇ ≡ bᵇ
  inj-⌜⌝ᵇ p = cong ⌞_⌟ p

  -- Universes
  opaque
    unfolding Setᵇ Elᵇ ⌜_⌝ᵇ

    Uᵇ : ∀ ℓ → Setᵇ (lsuc ℓ)
    Uᵇ ℓ = ⌞ (λ _ → Set ℓ) ⌟ᵇ

    russellᵇ : Setᵇ ℓ ≡ Elᵇ (Uᵇ ℓ)
    russellᵇ = refl

  {-# REWRITE russellᵇ #-}

  -- Type formers --

  -- ϕ modality of Elᵇ
  opaque
    joinᵇ : (ϕ → Elᵇ Aᵇ) → Elᵇ Aᵇ
    joinᵇ {Aᵇ = Aᵇ} f = ⌞ (λ p → ⌜_⌝ {Aᵇ = Aᵇ} (f p) p) ⌟

    weakᵇ : Elᵇ Aᵇ → (ϕ → Elᵇ Aᵇ)
    weakᵇ a _ = a

    join-weakᵇ : joinᵇ (λ _ → aᵇ) ≡ aᵇ
    join-weakᵇ = refl

    {-# REWRITE join-weakᵇ #-}

    weak-joinᵇ : (g : ϕ → Elᵇ Aᵇ) (p : ϕ) → g p ≡ joinᵇ g
    weak-joinᵇ g p = inj-⌜⌝ᵇ (propfunext (λ _ → refl))

  joinᵇ-natural : (h : Elᵇ Aᵇ → Elᵇ Bᵇ) (g : ϕ → Elᵇ Aᵇ)
    → joinᵇ (λ p → h (g p)) ≡ h (joinᵇ g)
  joinᵇ-natural h g = cong joinᵇ (propfunext (λ p → cong h (weak-joinᵇ g p)))

  -- Pi
  opaque
    Πᵇ : (Aᵇ : Setᵇ ℓ) → (Elᵇ Aᵇ → Setᵇ ℓ') → Setᵇ (ℓ ⊔ ℓ')
    Πᵇ Aᵇ Fᵇ = ⌞ (λ p → (x : ⌜ Aᵇ ⌝ᵇ p) → ⌜ Fᵇ ⌞ (λ _ → x) ⌟ ⌝ᵇ p) ⌟ᵇ

    lamᵇ : ((x : Elᵇ Aᵇ) → Elᵇ (Fᵇ x)) → Elᵇ (Πᵇ Aᵇ Fᵇ)
    lamᵇ f = ⌞ (λ p x → ⌜ f ⌞ (λ _ → x) ⌟ ⌝ p ) ⌟

    appᵇ : Elᵇ (Πᵇ Aᵇ Fᵇ) → (x : Elᵇ Aᵇ) → Elᵇ (Fᵇ x)
    appᵇ f x = ⌞ (λ p → ⌜ f ⌝ p (⌜ x ⌝ p)) ⌟

    Πβᵇ : appᵇ (lamᵇ fᵇ) aᵇ ≡ fᵇ aᵇ
    Πβᵇ = refl

    Πηᵇ : lamᵇ (appᵇ aᵇ) ≡ aᵇ
    Πηᵇ = refl

  {-# REWRITE Πβᵇ Πηᵇ #-}

  syntax Πᵇ Aᵇ (λ a → Fᵇ) = [ a ∈ᵇ Aᵇ ] ⇒ Fᵇ
  syntax lamᵇ (λ a → tᵇ)  = λᵇ a ⇒ tᵇ
  syntax appᵇ t u = t ∙ᵇ u

  -- Sigma
  opaque
    Σᵇ : (Aᵇ : Setᵇ ℓ) → (Elᵇ Aᵇ → Setᵇ ℓ') → Setᵇ (ℓ ⊔ ℓ')
    Σᵇ Aᵇ Fᵇ = ⌞ (λ p → Σ[ x ∈ ⌜ Aᵇ ⌝ᵇ p ] ⌜ Fᵇ ⌞ (λ _ → x) ⌟ ⌝ᵇ p) ⌟ᵇ

    pairᵇ : (a : Elᵇ Aᵇ) → Elᵇ (Fᵇ a) → Elᵇ (Σᵇ Aᵇ Fᵇ)
    pairᵇ a b = ⌞ (λ p → ⌜ a ⌝ p , ⌜ b ⌝ p ) ⌟

    fstᵇ : Elᵇ (Σᵇ Aᵇ Fᵇ) → Elᵇ Aᵇ
    fstᵇ ab = ⌞ (λ p → ⌜ ab ⌝ p .proj₁) ⌟

    Σfstᵇ : fstᵇ (pairᵇ aᵇ bᵇ) ≡ aᵇ
    Σfstᵇ = refl

    sndᵇ : (ab : Elᵇ (Σᵇ Aᵇ Fᵇ)) → Elᵇ (Fᵇ (fstᵇ ab))
    sndᵇ ab = ⌞ (λ p → ⌜ ab ⌝ p .proj₂) ⌟

    {-# REWRITE Σfstᵇ #-}

    Σsndᵇ : sndᵇ (pairᵇ aᵇ bᵇ) ≡ bᵇ
    Σsndᵇ = refl

    {-# REWRITE Σsndᵇ #-}

    Σηᵇ : pairᵇ (fstᵇ aᵇ) (sndᵇ aᵇ) ≡ aᵇ
    Σηᵇ = refl

    {-# REWRITE Σηᵇ #-}

  syntax Σᵇ Aᵇ (λ a → Fᵇ) = [ a ∈ᵇ Aᵇ ] × Fᵇ


  -- Unit
  opaque
    𝟙ᵇ : Setᵇ ℓ
    𝟙ᵇ {ℓ = ℓ} = ⌞ (λ _ → Lift ℓ 𝟙) ⌟ᵇ

    ttᵇ : Elᵇ (𝟙ᵇ {ℓ = ℓ})
    ttᵇ = ⌞ (λ _ → lift tt𝟙) ⌟

    𝟙ᵇη : aᵇ ≡ ttᵇ
    𝟙ᵇη = inj-⌜⌝ᵇ (propfunext (λ _ → refl))

  -- Equality
  opaque
    _≡ᵇ_ : {A : Set ℓ} → A → A → Setᵇ ℓ
    a ≡ᵇ b = ⌞ (λ _ → (a ≡ b) holds) ⌟ᵇ

    rflᵇ : Elᵇ {ℓ} (aᵇ ≡ᵇ aᵇ)
    rflᵇ = ⌞ (λ _ → by refl) ⌟

    reflectᵇ : Elᵇ {ℓ} (aᵇ ≡ᵇ bᵇ) → ϕ → aᵇ ≡ bᵇ
    reflectᵇ e p = ⌜ e ⌝ p .witness

    reflexᵇ : aᵇ ≡ bᵇ → Elᵇ {ℓ} (aᵇ ≡ᵇ bᵇ)
    reflexᵇ p = ⌞ (λ _ → by p) ⌟

  -- Booleans
  opaque
    𝟚ᵇ : Setᵇ ℓ
    𝟚ᵇ {ℓ = ℓ} = ⌞ (λ _ → Lift ℓ Bool) ⌟ᵇ

    trueᵇ : Elᵇ (𝟚ᵇ {ℓ = ℓ})
    trueᵇ = ⌞ (λ _ → lift Bool.true) ⌟

    falseᵇ : Elᵇ (𝟚ᵇ {ℓ = ℓ})
    falseᵇ = ⌞ (λ _ → lift Bool.false) ⌟

    ifᵇ_ret_then_else_ : ∀ {ℓ} (x : Elᵇ (𝟚ᵇ {ℓ = ℓ}))
      (P : Elᵇ 𝟚ᵇ → Setᵇ ℓ')
      → Elᵇ (P trueᵇ) → Elᵇ (P falseᵇ) → Elᵇ (P x)
    ifᵇ_ret_then_else_ x P a b = ⌞ (λ p → go p (⌜ x ⌝ p .Lift.lower)) ⌟
      where
        go : (p : ϕ) → (y : Bool) → ⌜ P (⌞ (λ _ → lift y) ⌟) ⌝ᵇ p
        go p Bool.true  = ⌜ a ⌝ p
        go p Bool.false = ⌜ b ⌝ p

    ifᵇtrue : ifᵇ trueᵇ ret Fᵇ then aᵇ else bᵇ ≡ aᵇ
    ifᵇtrue = refl

    ifᵇfalse : ifᵇ falseᵇ ret Fᵇ then aᵇ else bᵇ ≡ bᵇ
    ifᵇfalse = refl

  {-# REWRITE ifᵇtrue ifᵇfalse #-}

  ifᵇ_then_else : ∀ {Aᵇ} → Elᵇ (𝟚ᵇ {ℓ = ℓ}) → Elᵇ {ℓ = ℓ'} Aᵇ → Elᵇ Aᵇ → Elᵇ Aᵇ
  ifᵇ_then_else {Aᵇ = Aᵇ} x a b = ifᵇ x ret (λ _ → Aᵇ) then a else b
