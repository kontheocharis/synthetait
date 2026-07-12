module Gluing.Base where

open import Agda.Primitive
open import Utils
open import Data.Product
open import Data.Unit using () renaming (⊤ to 𝟙; tt to tt𝟙)
open import Data.Bool using (Bool)
open import Level using (Lift; lift)
open import Gluing.Realignment

module In (S : Set) (Φ : S → Prop) where
  private variable
    s : S
    ℓ ℓ' : Level

  private
    Setᵇ-iso : Φ s → Isomorph (Φ s → Set ℓ)
    Setᵇ-iso {ℓ = ℓ} ϕ = record
      { [_] = Set ℓ
      ; iso = record
          { to = λ f → f ϕ
          ; from = λ X _ → X
          ; to-from = λ _ → refl
          ; from-to = λ _ → refl
          }
      }

  -- Base universe
  -- This is the realigned version of Φ s → Set

  opaque
    Setᵇ : S → (ℓ : Level) → Set (lsuc ℓ)
    Setᵇ s ℓ = Realign (Φ s) (Φ s → Set ℓ) Setᵇ-iso

    Elᵇ-iso : (Aᵇ : Realign (Φ s) (Φ s → Set ℓ) Setᵇ-iso)
            → Φ s → Isomorph ((ϕ : Φ s) → ⌜ Aᵇ ⌝ᴿ ϕ)
    Elᵇ-iso Aᵇ ϕ = record
      { [_] = ⌜ Aᵇ ⌝ᴿ ϕ
      ; iso = record
          { to = λ f → f ϕ
          ; from = λ x _ → x
          ; to-from = λ _ → refl
          ; from-to = λ _ → refl
          }
      }

    Elᵇ : Setᵇ s ℓ → Set ℓ
    Elᵇ {s = s} Aᵇ = Realign (Φ s) ((ϕ : Φ s) → ⌜ Aᵇ ⌝ᴿ ϕ) (Elᵇ-iso Aᵇ)

  private variable
    Aᵇ Bᵇ Cᵇ : Setᵇ s ℓ
    Fᵇ Gᵇ : Elᵇ Aᵇ → Setᵇ s ℓ
    aᵇ bᵇ cᵇ : Elᵇ Aᵇ
    fᵇ gᵇ : (x : Elᵇ Aᵇ) → Elᵇ (Fᵇ x)
    A : Set ℓ
    A' B' : Φ s → Set ℓ
    f g : (p : Φ s) → A' p


  -- Wrap/unwrap
  opaque
    unfolding Setᵇ Elᵇ

    ⌞_⌟ᵇ : (Φ s → Set ℓ) → Setᵇ s ℓ
    ⌞ A ⌟ᵇ = ⌞ A ⌟ᴿ

    ⌜_⌝ᵇ : Setᵇ s ℓ → (Φ s → Set ℓ)
    ⌜ Aᵇ ⌝ᵇ = ⌜ Aᵇ ⌝ᴿ

    ⌜⌞⌟⌝ᵇ' : ∀ {A' : Φ s → Set ℓ} → ⌜ ⌞ A' ⌟ᵇ ⌝ᵇ ≡ A'
    ⌜⌞⌟⌝ᵇ' = refl

    ⌞⌜⌝⌟ᵇ' : ∀ {Aᵇ : Setᵇ s ℓ} → ⌞ ⌜ Aᵇ ⌝ᵇ ⌟ᵇ ≡ Aᵇ
    ⌞⌜⌝⌟ᵇ' = refl

    ⌞_⌟ : ((p : Φ s) → ⌜ Aᵇ ⌝ᵇ p) → Elᵇ Aᵇ
    ⌞ f ⌟ = ⌞ f ⌟ᴿ

    ⌜_⌝ : Elᵇ Aᵇ → (p : Φ s) → ⌜ Aᵇ ⌝ᵇ p
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

    Uᵇ : ∀ ℓ → Setᵇ s (lsuc ℓ)
    Uᵇ ℓ = ⌞ (λ _ → Set ℓ) ⌟ᵇ

    russellᵇ : Setᵇ s ℓ ≡ Elᵇ {s = s} (Uᵇ ℓ)
    russellᵇ = refl

  {-# REWRITE russellᵇ #-}

  -- Type formers --

  -- Φ modality of Elᵇ
  opaque
    joinᵇ : (Φ s → Elᵇ {s = s} Aᵇ) → Elᵇ Aᵇ
    joinᵇ {Aᵇ = Aᵇ} f = ⌞ (λ ϕ → ⌜_⌝ {Aᵇ = Aᵇ} (f ϕ) ϕ) ⌟

    weakᵇ : Elᵇ {s = s} Aᵇ → (Φ s → Elᵇ Aᵇ)
    weakᵇ a _ = a

    join-weakᵇ : joinᵇ (λ _ → aᵇ) ≡ aᵇ
    join-weakᵇ = refl

    {-# REWRITE join-weakᵇ #-}

    weak-joinᵇ : (g : Φ s → Elᵇ {s = s} Aᵇ) (ϕ : Φ s) → g ϕ ≡ joinᵇ g
    weak-joinᵇ g ϕ = inj-⌜⌝ᵇ (propfunext (λ _ → refl))

  joinᵇ-natural : (h : Elᵇ {s = s} Aᵇ → Elᵇ Bᵇ) (g : Φ s → Elᵇ Aᵇ)
                → joinᵇ (λ ϕ → h (g ϕ)) ≡ h (joinᵇ g)
  joinᵇ-natural h g = cong joinᵇ (propfunext (λ ϕ → cong h (weak-joinᵇ g ϕ)))

  -- Pi
  opaque
    Πᵇ : (Aᵇ : Setᵇ s ℓ) → (Elᵇ Aᵇ → Setᵇ s ℓ') → Setᵇ s (ℓ ⊔ ℓ')
    Πᵇ Aᵇ Fᵇ = ⌞ (λ ϕ → (x : ⌜ Aᵇ ⌝ᵇ ϕ) → ⌜ Fᵇ ⌞ (λ _ → x) ⌟ ⌝ᵇ ϕ) ⌟ᵇ

    lamᵇ : ((x : Elᵇ Aᵇ) → Elᵇ (Fᵇ x)) → Elᵇ (Πᵇ Aᵇ Fᵇ)
    lamᵇ f = ⌞ (λ ϕ x → ⌜ f ⌞ (λ _ → x) ⌟ ⌝ ϕ ) ⌟

    appᵇ : Elᵇ (Πᵇ Aᵇ Fᵇ) → (x : Elᵇ Aᵇ) → Elᵇ (Fᵇ x)
    appᵇ f x = ⌞ (λ ϕ → ⌜ f ⌝ ϕ (⌜ x ⌝ ϕ)) ⌟

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
    Σᵇ : (Aᵇ : Setᵇ s ℓ) → (Elᵇ Aᵇ → Setᵇ s ℓ') → Setᵇ s (ℓ ⊔ ℓ')
    Σᵇ Aᵇ Fᵇ = ⌞ (λ ϕ → Σ[ x ∈ ⌜ Aᵇ ⌝ᵇ ϕ ] ⌜ Fᵇ ⌞ (λ _ → x) ⌟ ⌝ᵇ ϕ) ⌟ᵇ

    pairᵇ : (a : Elᵇ Aᵇ) → Elᵇ (Fᵇ a) → Elᵇ (Σᵇ Aᵇ Fᵇ)
    pairᵇ a b = ⌞ (λ ϕ → ⌜ a ⌝ ϕ , ⌜ b ⌝ ϕ ) ⌟

    fstᵇ : Elᵇ (Σᵇ Aᵇ Fᵇ) → Elᵇ Aᵇ
    fstᵇ p = ⌞ (λ ϕ → ⌜ p ⌝ ϕ .proj₁) ⌟

    Σfstᵇ : fstᵇ (pairᵇ aᵇ bᵇ) ≡ aᵇ
    Σfstᵇ = refl

    sndᵇ : (p : Elᵇ (Σᵇ Aᵇ Fᵇ)) → Elᵇ (Fᵇ (fstᵇ p))
    sndᵇ p = ⌞ (λ ϕ → ⌜ p ⌝ ϕ .proj₂) ⌟

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
    𝟙ᵇ : Setᵇ s ℓ
    𝟙ᵇ {ℓ = ℓ} = ⌞ (λ _ → Lift ℓ 𝟙) ⌟ᵇ

    ttᵇ : Elᵇ (𝟙ᵇ {s = s} {ℓ = ℓ})
    ttᵇ = ⌞ (λ _ → lift tt𝟙) ⌟

    𝟙ᵇη : aᵇ ≡ ttᵇ
    𝟙ᵇη = inj-⌜⌝ᵇ (propfunext (λ _ → refl))

  -- Equality
  opaque
    _≡ᵇ_ : {A : Set ℓ} → A → A → Setᵇ s ℓ
    a ≡ᵇ b = ⌞ (λ _ → (a ≡ b) holds) ⌟ᵇ

    rflᵇ : Elᵇ {s} {ℓ} (aᵇ ≡ᵇ aᵇ)
    rflᵇ = ⌞ (λ _ → by refl) ⌟

    reflectᵇ : Elᵇ {s} {ℓ} (aᵇ ≡ᵇ bᵇ) → Φ s → aᵇ ≡ bᵇ
    reflectᵇ p ϕ = ⌜ p ⌝ ϕ .witness

    reflexᵇ : aᵇ ≡ bᵇ → Elᵇ {s} {ℓ} (aᵇ ≡ᵇ bᵇ)
    reflexᵇ p = ⌞ (λ _ → by p) ⌟

  -- Booleans
  opaque
    𝟚ᵇ : Setᵇ s ℓ
    𝟚ᵇ {ℓ = ℓ} = ⌞ (λ _ → Lift ℓ Bool) ⌟ᵇ

    trueᵇ : Elᵇ (𝟚ᵇ {s = s} {ℓ = ℓ})
    trueᵇ = ⌞ (λ _ → lift Bool.true) ⌟

    falseᵇ : Elᵇ (𝟚ᵇ {s = s} {ℓ = ℓ})
    falseᵇ = ⌞ (λ _ → lift Bool.false) ⌟

    ifᵇ_ret_then_else_ : ∀ {s ℓ} (x : Elᵇ (𝟚ᵇ {s = s} {ℓ = ℓ}))
        (P : Elᵇ 𝟚ᵇ → Setᵇ s ℓ')
        → Elᵇ (P trueᵇ) → Elᵇ (P falseᵇ) → Elᵇ (P x)
    ifᵇ_ret_then_else_ {s = s} x P a b = ⌞ (λ ϕ → go ϕ (⌜ x ⌝ ϕ .Lift.lower)) ⌟
      where
        go : (ϕ : Φ s) → (y : Bool) → ⌜ P (⌞ (λ _ → lift y) ⌟) ⌝ᵇ ϕ
        go ϕ Bool.true  = ⌜ a ⌝ ϕ
        go ϕ Bool.false = ⌜ b ⌝ ϕ

    ifᵇtrue : ifᵇ trueᵇ ret Fᵇ then aᵇ else bᵇ ≡ aᵇ
    ifᵇtrue = refl

    ifᵇfalse : ifᵇ falseᵇ ret Fᵇ then aᵇ else bᵇ ≡ bᵇ
    ifᵇfalse = refl

  {-# REWRITE ifᵇtrue ifᵇfalse #-}

  ifᵇ_then_else : ∀ {Aᵇ} → Elᵇ (𝟚ᵇ {s = s} {ℓ = ℓ}) → Elᵇ {ℓ = ℓ'} Aᵇ → Elᵇ Aᵇ → Elᵇ Aᵇ
  ifᵇ_then_else {Aᵇ = Aᵇ} x a b = ifᵇ x ret (λ _ → Aᵇ) then a else b
