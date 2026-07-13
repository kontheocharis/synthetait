module Gluing.Unary where

open import Agda.Primitive
open import Utils
open import Data.Product
open import Data.Unit using () renaming (⊤ to 𝟙; tt to tt𝟙)
open import Data.Bool using (Bool)
open import Level using (Lift; lift)
open import Gluing.Realignment
import Gluing.Base as Base

module In (ϕ : Prop) where
  open Base.In 𝟙 (λ _ → ϕ) public

  private variable
    ℓ ℓ' : Level
    A B C : Set ℓ
    Aᵇ Bᵇ Cᵇ : Setᵇ tt𝟙 ℓ
    Fᵇ Gᵇ : Elᵇ Aᵇ → Setᵇ tt𝟙 ℓ
    aᵇ bᵇ cᵇ : Elᵇ Aᵇ
    fᵇ gᵇ : (x : Elᵇ Aᵇ) → Elᵇ (Fᵇ x)

  -- Fiber universe
  -- Setᶠ-𝟙 ℓ is a closed-modal type
  -- Setᶠ Aᵇ is an Elᵇ Aᵇ-indexed (open-modal indexed) family of Setᶠ-𝟙 values.

  Setᶠ-𝟙 : (ℓ : Level) → Set (lsuc ℓ)
  Setᶠ-𝟙 ℓ = Σ[ X ∈ Set ℓ ] (ϕ → (X ≡ Lift ℓ 𝟙) holds)

  ϕ→⋆-contr : ∀ {A : Set ℓ} → (p : ϕ) → (ϕ ⋆ A) ≃ Lift ℓ 𝟙
  ϕ→⋆-contr p .to _ = lift tt𝟙
  ϕ→⋆-contr p .from _ = ϕ-pt⋆ p
  ϕ→⋆-contr p .to-from _ = refl
  ϕ→⋆-contr p .from-to x = sym (collapse⋆ p x)

  Setᶠ-𝟙-contr : ∀ {Aᵇ : Setᵇ tt𝟙 ℓ} → (p : ϕ) → (Elᵇ Aᵇ → Setᶠ-𝟙 ℓ) ≃ Lift (lsuc ℓ) 𝟙
  Setᶠ-𝟙-contr p .to _ = lift tt𝟙
  Setᶠ-𝟙-contr p .from _ aᵇ = Lift _ 𝟙 , (λ _ → by refl)
  Setᶠ-𝟙-contr p .to-from _ = refl
  Setᶠ-𝟙-contr p .from-to Aᶠ =
    funext (λ aᵇ → Σ≡ (sym (Aᶠ aᵇ .proj₂ p .witness)) (propfunext (λ q → refl)))

  -- This is Elᵇ Aᵇ → Setᶠ-𝟙 ℓ realigned over unit. This will allow us to have a Russell hierarchy.
  opaque
    Setᶠ : Setᵇ tt𝟙 ℓ → Set (lsuc ℓ)
    Setᶠ {ℓ = ℓ} Aᵇ =
      Realign ϕ (Elᵇ Aᵇ → Setᶠ-𝟙 ℓ) (λ p → record { [_] = Lift _ 𝟙 ; iso = Setᶠ-𝟙-contr p })

    Elᶠ : {Aᵇ : Setᵇ tt𝟙 ℓ} → Setᶠ Aᵇ → Elᵇ Aᵇ → Set ℓ
    Elᶠ Aᶠ aᵇ = ⌜ Aᶠ ⌝ᴿ aᵇ .proj₁

  private variable
    Aᶠ Bᶠ Cᶠ : Setᶠ Aᵇ
    Fᶠ Gᶠ : ∀ {xᵇ} → Elᶠ Aᶠ xᵇ → Setᶠ (Fᵇ xᵇ)
    aᶠ bᶠ cᶠ tᶠ tᶠ' uᶠ uᶠ' : Elᶠ Aᶠ aᵇ
    fᶠ gᶠ : ∀ {xᵇ} (xᶠ : Elᶠ Aᶠ xᵇ) → Elᶠ (Fᶠ xᶠ) (fᵇ xᵇ)
    F G : Elᵇ Aᵇ → Setᶠ {ℓ = ℓ} 𝟙ᵇ
    S T : Setᶠ-𝟙 ℓ

  _* : Elᶠ {ℓ = ℓ} {Aᵇ = Aᵇ} Aᶠ aᵇ → Elᵇ {ℓ = ℓ} Aᵇ
  _* {aᵇ = aᵇ} _ = aᵇ

  opaque
    unfolding coe
    ap-Elᶠᵇ : aᵇ ≡ bᵇ → Elᶠ Aᶠ aᵇ ≡ Elᶠ Aᶠ bᵇ
    ap-Elᶠᵇ refl = refl
    
    ap-ElᶠT : Aᶠ ≡ Bᶠ → Elᶠ Aᶠ aᵇ ≡ Elᶠ Bᶠ aᵇ
    ap-ElᶠT refl = refl

  -- Setᶠ-𝟙 ⇄ Setᶠ 𝟙ᵇ
  opaque
    unfolding Setᶠ

    ⌞_⌟ᶠ : Setᶠ-𝟙 ℓ → Setᶠ {ℓ = ℓ} 𝟙ᵇ
    ⌞ S ⌟ᶠ = ⌞ (λ _ → S) ⌟ᴿ

    ⌜_⌝ᶠ : Setᶠ {ℓ = ℓ} 𝟙ᵇ → Setᶠ-𝟙 ℓ
    ⌜ Aᶠ ⌝ᶠ = ⌜ Aᶠ ⌝ᴿ ttᵇ

    ⌜⌞⌟⌝ᶠ : ⌜ ⌞ S ⌟ᶠ ⌝ᶠ ≡ S
    ⌜⌞⌟⌝ᶠ = refl

    ⌞⌜⌝⌟ᶠ : ⌞ ⌜ Aᶠ ⌝ᶠ ⌟ᶠ ≡ Aᶠ
    ⌞⌜⌝⌟ᶠ {Aᶠ = Aᶠ} = cong ⌞_⌟ᴿ (funext {g = ⌜ Aᶠ ⌝ᴿ} (λ x → cong ⌜ Aᶠ ⌝ᴿ (sym 𝟙ᵇη)))

    {-# INJECTIVE ⌞_⌟ᶠ #-}

  -- S .proj₁ ⇄ Elᶠ {𝟙ᵇ} ⌞ S ⌟ᶠ ttᵇ
  opaque
    unfolding Setᶠ Elᶠ ⌞_⌟ᶠ

    wrap : S .proj₁ → Elᶠ {Aᵇ = 𝟙ᵇ} ⌞ S ⌟ᶠ ttᵇ
    wrap x = x

    unwrap : Elᶠ {Aᵇ = 𝟙ᵇ} ⌞ S ⌟ᶠ ttᵇ → S .proj₁
    unwrap x = x

    unwrap-wrap : ∀ {ℓ} {S : Setᶠ-𝟙 ℓ} {x : S .proj₁} → unwrap {S = S} (wrap {S = S} x) ≡ x
    unwrap-wrap = refl

    wrap-unwrap : ∀ {ℓ} {S : Setᶠ-𝟙 ℓ} {y : Elᶠ {Aᵇ = 𝟙ᵇ} ⌞ S ⌟ᶠ ttᵇ} → wrap {S = S} (unwrap {S = S} y) ≡ y
    wrap-unwrap = refl

  {-# REWRITE unwrap-wrap wrap-unwrap #-}

  -- Glue/Ext: Setᶠ Aᵇ ⇄ (Elᵇ Aᵇ → Setᶠ 𝟙ᵇ)
  opaque
    unfolding Setᶠ Elᶠ ⌞_⌟ᶠ ⌜_⌝ᶠ

    Glue : (Elᵇ {ℓ = ℓ} Aᵇ → Setᶠ {ℓ = ℓ} 𝟙ᵇ) → Setᶠ Aᵇ
    Glue F = ⌞ (λ aᵇ → ⌜ F aᵇ ⌝ᶠ) ⌟ᴿ

    Ext : Setᶠ {ℓ = ℓ} Aᵇ → (Elᵇ Aᵇ → Setᶠ {ℓ = ℓ} 𝟙ᵇ)
    Ext Aᶠ aᵇ = ⌞ ⌜ Aᶠ ⌝ᴿ aᵇ ⌟ᶠ

    Glue-Ext : Glue (Ext Aᶠ) ≡ Aᶠ
    Glue-Ext = refl

    Ext-Glue : Ext (Glue F) ≡ F
    Ext-Glue = funext (λ aᵇ → ⌞⌜⌝⌟ᶠ)

    glue : Elᶠ {Aᵇ = 𝟙ᵇ} (F aᵇ) ttᵇ → Elᶠ (Glue F) aᵇ
    glue x = x

    unglue : Elᶠ (Glue F) aᵇ → Elᶠ {Aᵇ = 𝟙ᵇ} (F aᵇ) ttᵇ
    unglue x = x

    unglue-glue : ∀ {x : Elᶠ {Aᵇ = 𝟙ᵇ} (F aᵇ) ttᵇ} → unglue (glue {F = F} {aᵇ = aᵇ} x) ≡ x
    unglue-glue = refl

    glue-unglue : ∀ {y : Elᶠ (Glue F) aᵇ} → glue (unglue {F = F} {aᵇ = aᵇ} y) ≡ y
    glue-unglue = refl

    ext : Elᶠ Aᶠ aᵇ → Elᶠ {Aᵇ = 𝟙ᵇ} (Ext Aᶠ aᵇ) ttᵇ
    ext x = x

    unext : Elᶠ {Aᵇ = 𝟙ᵇ} (Ext Aᶠ aᵇ) ttᵇ → Elᶠ Aᶠ aᵇ
    unext x = x

    unext-ext : ∀ {x : Elᶠ Aᶠ aᵇ} → unext (ext {Aᶠ = Aᶠ} {aᵇ = aᵇ} x) ≡ x
    unext-ext = refl

    ext-unext : ∀ {y : Elᶠ {Aᵇ = 𝟙ᵇ} (Ext Aᶠ aᵇ) ttᵇ} → ext (unext {Aᶠ = Aᶠ} {aᵇ = aᵇ} y) ≡ y
    ext-unext = refl

    into : ⌜ Ext Aᶠ aᵇ ⌝ᶠ .proj₁ → Elᶠ Aᶠ aᵇ
    into x = x

    out : Elᶠ Aᶠ aᵇ → ⌜ Ext Aᶠ aᵇ ⌝ᶠ .proj₁
    out x = x

    out-into : ∀ {x : ⌜ Ext Aᶠ aᵇ ⌝ᶠ .proj₁} → out {Aᶠ = Aᶠ} {aᵇ = aᵇ} (into x) ≡ x
    out-into = refl

    into-out : ∀ {y : Elᶠ Aᶠ aᵇ} → into {Aᶠ = Aᶠ} {aᵇ = aᵇ} (out y) ≡ y
    into-out = refl

    {-# INJECTIVE Glue #-}

  {-# REWRITE unglue-glue glue-unglue unext-ext ext-unext out-into into-out #-}

  -- Unit eta is annoying:
  opaque
    unfolding ext unext coe
    unext-coe-ext : unext (coe (ap-Elᶠᵇ 𝟙ᵇη) (ext aᶠ)) ≡ aᶠ
    unext-coe-ext = refl
  {-# REWRITE unext-coe-ext #-}

  inj-Glue : Glue F ≡ Glue G → F ≡ G
  inj-Glue p = trans (sym Ext-Glue) (trans (cong Ext p) Ext-Glue)

  inj-Ext : Ext Aᶠ ≡ Ext Bᶠ → Aᶠ ≡ Bᶠ
  inj-Ext p = trans (sym Glue-Ext) (trans (cong Glue p) Glue-Ext)

  syntax Ext Aᶠ aᵇ = [ Aᶠ ↪ aᵇ ]
  syntax Glue (λ a → F) = G[ a ∈ᶠ ] F

  Glue′ : (Aᵇ : Setᵇ tt𝟙 ℓ) → (Elᵇ Aᵇ → Setᶠ {ℓ = ℓ} 𝟙ᵇ) → Setᶠ Aᵇ
  Glue′ _ F = Glue F

  syntax Glue′ Aᵇ (λ a → F) = G[ a ∈ Aᵇ ] F

  private variable
    Yᶠ : (xᵇ : Elᵇ Aᵇ) → Setᶠ (Fᵇ xᵇ)

  ∣_∣ : Elᶠ (G[ x ∈ᶠ ] [ Yᶠ x ↪ fᵇ x ]) aᵇ → Elᶠ (Yᶠ aᵇ) (fᵇ aᵇ)
  ∣ p ∣ = unext (unglue p)

  ⟨_⟩ : Elᶠ (Yᶠ aᵇ) (fᵇ aᵇ) → Elᶠ (G[ x ∈ᶠ ] [ Yᶠ x ↪ fᵇ x ]) aᵇ
  ⟨ p ⟩ = glue (ext p)

  ap-⟨⟩ : (e : aᵇ ≡ bᵇ)
    {w₁ : Elᶠ (Yᶠ aᵇ) (fᵇ aᵇ)} {w₂ : Elᶠ (Yᶠ bᵇ) (fᵇ bᵇ)}
    → w₁ ≡[ cong (λ z → Elᶠ (Yᶠ z) (fᵇ z)) e ] w₂
    → ⟨_⟩ {Yᶠ = Yᶠ} {fᵇ = fᵇ} w₁ ≡[ ap-Elᶠᵇ e ] ⟨ w₂ ⟩
  ap-⟨⟩ refl q = dep (cong ⟨_⟩ (undep q))

  -- Generic reindexing
  reindex : (Elᵇ {ℓ = ℓ} Aᵇ → Elᵇ {ℓ = ℓ} Bᵇ) → Setᶠ Bᵇ → Setᶠ Aᵇ
  reindex f Aᶠ = G[ t ∈ᶠ ] [ Aᶠ ↪ f t ]

  -- -- Type formers --

  private
    contr : (A ≡ Lift ℓ 𝟙) holds → (x y : A) → x ≡ y
    contr (by refl) x y = refl

    pt : (A ≡ Lift ℓ 𝟙) holds → A
    pt e = coe (sym (e .witness)) (lift tt𝟙)

  -- Pi
  opaque
    Πᶠ : (Aᶠ : Setᶠ Aᵇ) → (∀ {aᵇ} → Elᶠ Aᶠ aᵇ → Setᶠ (Fᵇ aᵇ)) → Setᶠ (Πᵇ Aᵇ Fᵇ)
    Πᶠ {Aᵇ = Aᵇ} {Fᵇ = Fᵇ} Aᶠ Fᶠ = Glue (λ f → ⌞
        Realign ϕ (∀ {aᵇ} (aᶠ : Elᶠ Aᶠ aᵇ) → Elᶠ (Fᶠ aᶠ) (appᵇ f aᵇ)) (λ p →
          record
            { [_] = Lift _ 𝟙
            ; iso = record
                { to = λ _ → lift tt𝟙
                ; from = λ _ {aᵇ} aᶠ →
                    into (pt (⌜ Ext (Fᶠ aᶠ) (appᵇ f aᵇ) ⌝ᶠ .proj₂ p))
                ; to-from = λ _ → refl
                ; from-to = λ g → ifunext λ aᵇ → funext λ aᶠ →
                    cong into
                      (contr (⌜ Ext (Fᶠ aᶠ) (appᵇ f aᵇ) ⌝ᶠ .proj₂ p)
                        (pt (⌜ Ext (Fᶠ aᶠ) (appᵇ f aᵇ) ⌝ᶠ .proj₂ p))
                        (out (g aᶠ)))
                }
            }) ,
        (λ p → by (ϕ→Realign p))
      ⌟ᶠ)

    lamᶠ : (∀ {aᵇ} (aᶠ : Elᶠ Aᶠ aᵇ) → Elᶠ (Fᶠ aᶠ) (fᵇ aᵇ))
         → Elᶠ (Πᶠ Aᶠ Fᶠ) (lamᵇ fᵇ)
    lamᶠ f = glue (wrap ⌞ (λ {aᵇ} aᶠ → f aᶠ) ⌟ᴿ)

    appᶠ : Elᶠ (Πᶠ Aᶠ Fᶠ) aᵇ → ∀ {bᵇ} (bᶠ : Elᶠ Aᶠ bᵇ) → Elᶠ (Fᶠ bᶠ) (appᵇ aᵇ bᵇ)
    appᶠ t bᶠ = ⌜ unwrap (unglue t) ⌝ᴿ bᶠ

    Πβᶠ : appᶠ {Aᶠ = Aᶠ} {Fᶠ = Fᶠ} (lamᶠ fᶠ) aᶠ ≡ fᶠ aᶠ
    Πβᶠ = refl

    Πηᶠ : {tᶠ : Elᶠ (Πᶠ Aᶠ Fᶠ) (lamᵇ fᵇ)}
        → lamᶠ (appᶠ {Aᶠ = Aᶠ} {Fᶠ = Fᶠ} tᶠ) ≡ tᶠ
    Πηᶠ = refl

  {-# REWRITE Πβᶠ Πηᶠ #-}

  syntax Πᶠ Aᶠ (λ a → Fᶠ) = [ a ∈ᶠ Aᶠ ] ⇒ Fᶠ
  syntax lamᶠ (λ a → tᶠ) = λᶠ a ⇒ tᶠ
  syntax appᶠ t u = t ∙ᶠ u

  ap-lamᶠ : (e : fᵇ ≡ gᵇ)
    {G₁ : ∀ {xᵇ} (xᶠ : Elᶠ Aᶠ xᵇ) → Elᶠ (Fᶠ xᶠ) (fᵇ xᵇ)}
    (G₂ : ∀ {xᵇ} (xᶠ : Elᶠ Aᶠ xᵇ) → Elᶠ (Fᶠ xᶠ) (gᵇ xᵇ))
    → (∀ {xᵇ} (xᶠ : Elᶠ Aᶠ xᵇ) → G₁ xᶠ ≡[ ap-Elᶠᵇ (ap-$ e xᵇ) ] G₂ xᶠ)
    → lamᶠ {Fᶠ = Fᶠ} {fᵇ = fᵇ} G₁ ≡[ cong (λ f → Elᶠ (Πᶠ Aᶠ Fᶠ) (lamᵇ f)) e ] lamᶠ G₂
  ap-lamᶠ refl G₂ q = dep (cong lamᶠ (ifunext (λ xᵇ → funext (λ xᶠ → undep (q xᶠ)))))

  -- Sigma
  opaque
    Σᶠ : (Aᶠ : Setᶠ Aᵇ) → (∀ {aᵇ} → Elᶠ Aᶠ aᵇ → Setᶠ (Fᵇ aᵇ)) → Setᶠ (Σᵇ Aᵇ Fᵇ)
    Σᶠ {Aᵇ = Aᵇ} {Fᵇ = Fᵇ} Aᶠ Fᶠ = Glue (λ p → ⌞
        Realign ϕ
          (Σ[ aᶠ ∈ Elᶠ Aᶠ (fstᵇ p) ] Elᶠ (Fᶠ aᶠ) (sndᵇ p))
          (λ p' → record
            { [_] = Lift _ 𝟙
            ; iso = record
                { to = λ _ → lift tt𝟙
                ; from = λ _ →
                    let aᶠ = into (pt (⌜ Ext Aᶠ (fstᵇ p) ⌝ᶠ .proj₂ p'))
                        bᶠ = into (pt (⌜ Ext (Fᶠ aᶠ) (sndᵇ p) ⌝ᶠ .proj₂ p'))
                    in aᶠ , bᶠ
                ; to-from = λ { (lift tt𝟙) → refl }
                ; from-to = λ q →
                    let aᶠ-x = into (pt (⌜ Ext Aᶠ (fstᵇ p) ⌝ᶠ .proj₂ p'))
                        bᶠ-x = into (pt (⌜ Ext (Fᶠ aᶠ-x) (sndᵇ p) ⌝ᶠ .proj₂ p'))
                        eq-a : aᶠ-x ≡ q .proj₁
                        eq-a = cong into (contr (⌜ Ext Aᶠ (fstᵇ p) ⌝ᶠ .proj₂ p')
                          (pt (⌜ Ext Aᶠ (fstᵇ p) ⌝ᶠ .proj₂ p'))
                          (out (q .proj₁)))
                        bᶠ' = subst (λ z → Elᶠ (Fᶠ z) (sndᵇ p)) eq-a bᶠ-x
                    in Σ≡ eq-a (cong into (contr (⌜ Ext (Fᶠ (q .proj₁)) (sndᵇ p) ⌝ᶠ .proj₂ p')
                      (out bᶠ') (out (q .proj₂))))
                }
            }) ,
        (λ p' → by (ϕ→Realign p'))
      ⌟ᶠ)

    pairᶠ : (xᶠ : Elᶠ Aᶠ aᵇ) → Elᶠ (Fᶠ xᶠ) bᵇ → Elᶠ (Σᶠ Aᶠ Fᶠ) (pairᵇ aᵇ bᵇ)
    pairᶠ aᶠ bᶠ = glue (wrap ⌞ aᶠ , bᶠ ⌟ᴿ)

    fstᶠ : Elᶠ (Σᶠ Aᶠ Fᶠ) aᵇ → Elᶠ Aᶠ (fstᵇ aᵇ)
    fstᶠ p = ⌜ unwrap (unglue p) ⌝ᴿ .proj₁

    sndᶠ : (p : Elᶠ (Σᶠ Aᶠ Fᶠ) aᵇ) → Elᶠ (Fᶠ (fstᶠ p)) (sndᵇ aᵇ)
    sndᶠ p = ⌜ unwrap (unglue p) ⌝ᴿ .proj₂

    Σfstᶠ : fstᶠ (pairᶠ {Aᶠ = Aᶠ} {Fᶠ = Fᶠ} aᶠ bᶠ) ≡ aᶠ
    Σfstᶠ = refl

    {-# REWRITE Σfstᶠ #-}

    Σsndᶠ : sndᶠ (pairᶠ {Aᶠ = Aᶠ} {Fᶠ = Fᶠ} aᶠ bᶠ) ≡ bᶠ
    Σsndᶠ = refl

    Σηᶠ : pairᶠ {Aᶠ = Aᶠ} {Fᶠ = Fᶠ} (fstᶠ aᶠ) (sndᶠ aᶠ) ≡ aᶠ
    Σηᶠ = refl

  {-# REWRITE Σsndᶠ Σηᶠ #-}

  syntax Σᶠ Aᶠ (λ a → Fᶠ) = [ a ∈ᶠ Aᶠ ] × Fᶠ

  -- Unit
  opaque
    𝟙ᶠ : Setᶠ {ℓ = ℓ} 𝟙ᵇ
    𝟙ᶠ {ℓ = ℓ} = Glue (λ _ → ⌞ Lift ℓ 𝟙 , (λ _ → by refl) ⌟ᶠ)

    ttᶠ : Elᶠ {Aᵇ = 𝟙ᵇ {ℓ = ℓ}} 𝟙ᶠ ttᵇ
    ttᶠ = glue (wrap (lift tt𝟙))

  -- Open immersion
  opaque
    ○ : (Aᵇ : Setᵇ tt𝟙 ℓ) → Setᶠ Aᵇ
    ○ {ℓ = ℓ} Aᵇ = Glue (λ _ → ⌞ Lift ℓ 𝟙 , (λ _ → by refl) ⌟ᶠ)

    η○ : ∀ aᵇ → Elᶠ (○ Aᵇ) aᵇ
    η○ _ = glue (wrap (lift tt𝟙))

  opaque
    unfolding ○ η○ Setᶠ Elᶠ ⌞_⌟ᶠ ⌜_⌝ᶠ Glue glue wrap

    η○-contr : η○ aᵇ ≡ bᶠ
    η○-contr = refl

  -- Closed modality
  opaque
    unfolding Πᶠ

    ● : Setᶠ {ℓ = ℓ} Aᵇ → Setᶠ (𝟙ᵇ {ℓ = ℓ})
    ● {Aᵇ = Aᵇ} Aᶠ = Glue (λ _ → ⌞
        Realign ϕ (ϕ ⋆ (Σ[ aᵇ ∈ Elᵇ Aᵇ ] Elᶠ Aᶠ aᵇ))
          (λ p → record { [_] = Lift _ 𝟙 ; iso = ϕ→⋆-contr p })
        , (λ p → by (ϕ→Realign p)) ⌟ᶠ)

    η● : Elᶠ Aᶠ aᵇ → Elᶠ (● Aᶠ) ttᵇ
    η● {aᵇ = aᵇ} aᶠ = glue (wrap ⌞ η⋆ (aᵇ , aᶠ) ⌟ᴿ)

    elim-● : (Pᶠ : ∀ (x : Elᶠ (● Aᶠ) ttᵇ) → Setᶠ (𝟙ᵇ {ℓ = ℓ}))
           → (η●ᴹ : ∀ {aᵇ} (aᶠ : Elᶠ Aᶠ aᵇ) → Elᶠ (Pᶠ (η● aᶠ)) ttᵇ)
           → ∀ aᶠ → Elᶠ (Pᶠ aᶠ) ttᵇ
    elim-● Pᶠ η●ᴹ x = into (elim⋆
      (λ y → ⌜ Ext (Pᶠ (glue (wrap ⌞ y ⌟ᴿ))) ttᵇ ⌝ᶠ .proj₁)
      (λ { (aᵇ , aᶠ) → out (η●ᴹ aᶠ) })
      (λ p → pt (⌜ Ext (Pᶠ (glue (wrap ⌞ ϕ-pt⋆ p ⌟ᴿ))) ttᵇ ⌝ᶠ .proj₂ p))
      (λ p (aᵇ , aᶠ) →
        contr (⌜ Ext (Pᶠ (glue (wrap ⌞ ϕ-pt⋆ p ⌟ᴿ))) ttᵇ ⌝ᶠ .proj₂ p) _ _)
      (⌜ unwrap (unglue x) ⌝ᴿ))

    elim-●-η● : ∀ {Pᶠ : Elᶠ (● Aᶠ) ttᵇ → Setᶠ (𝟙ᵇ {ℓ = ℓ})}
      {η●ᴹ : ∀ {aᵇ} (aᶠ : Elᶠ Aᶠ aᵇ) → Elᶠ (Pᶠ (η● aᶠ)) ttᵇ}
      → elim-● Pᶠ η●ᴹ (η● {aᵇ = aᵇ} aᶠ) ≡ η●ᴹ aᶠ
    elim-●-η● = refl

  {-# REWRITE elim-●-η● #-}

  _>>=_ : Elᶠ (● Aᶠ) ttᵇ → (∀ {aᵇ} (aᶠ : Elᶠ Aᶠ aᵇ) → Elᶠ Bᶠ ttᵇ) → Elᶠ Bᶠ ttᵇ
  _>>=_ {Bᶠ = Bᶠ} x f = elim-● (λ _ → Bᶠ) f x

  -- If the total space of Aᶠ is a prop, so is `● Aᶠ`.
  opaque
    unfolding ● Setᶠ Elᶠ Glue ⌞_⌟ᶠ ⌜_⌝ᶠ
    ●-prop : (∀ (s t : Σ[ aᵇ ∈ Elᵇ Aᵇ ] Elᶠ Aᶠ aᵇ) → s ≡ t) → (x y : Elᶠ (● Aᶠ) ttᵇ) → x ≡ y
    ●-prop tot-prop x y = inj-Realign (⋆-prop tot-prop ⌜ x ⌝ᴿ ⌜ y ⌝ᴿ)

  -- Prop elimination of `● Aᶠ`
  opaque
    unfolding ● Setᶠ Elᶠ Glue glue wrap ⌞_⌟ᶠ ⌜_⌝ᶠ η●

    elim-●-propᴰ : ∀ {ℓ'} (Pᶠ : Elᶠ (● Aᶠ) ttᵇ → Prop ℓ')
      → (∀ {aᵇ} (aᶠ : Elᶠ Aᶠ aᵇ) → Pᶠ (η● aᶠ))
      → ((p : ϕ) (w : Elᶠ (● Aᶠ) ttᵇ) → Pᶠ w)
      → (w : Elᶠ (● Aᶠ) ttᵇ) → Pᶠ w
    elim-●-propᴰ Pᶠ fη fϕ w =
      elim⋆ (λ s → Pᶠ ⌞ s ⌟ᴿ holds)
        (λ { (aᵇ , aᶠ) → by (fη aᶠ) })
        (λ p → by (fϕ p _))
        (λ p s → true-prop _ _)
        ⌜ w ⌝ᴿ .witness

  ⌞⌟ᵇ-prop : (∀ (x y : A) → x ≡ y) → (a b : Elᵇ ⌞ (λ _ → A) ⌟ᵇ) → a ≡ b
  ⌞⌟ᵇ-prop A-prop a b = inj-⌜⌝ᵇ (propfunext (λ p → A-prop (⌜ a ⌝ p) (⌜ b ⌝ p)))

  ○-tot-prop : (∀ (a b : Elᵇ Aᵇ) → a ≡ b) → (s t : Σ[ aᵇ ∈ Elᵇ Aᵇ ] Elᶠ (○ Aᵇ) aᵇ) → s ≡ t
  ○-tot-prop base-prop (a , x) (b , y) = Σ≡ (base-prop a b) (trans (sym η○-contr) η○-contr)

  -- Total fracture: embedding of an Agda Set as a fiber over its base
  opaque
    ⌞_⌟ᶠᶜ : (X : Set ℓ) → Setᶠ ⌞ (λ _ → X) ⌟ᵇ
    ⌞ X ⌟ᶠᶜ = Glue (λ aᵇ → ⌞
        Realign ϕ (ϕ ⋆ (Σ[ x ∈ X ] ((q : ϕ) → ⌜ aᵇ ⌝ q ≡ x) holds))
          (λ p → record { [_] = Lift _ 𝟙 ; iso = ϕ→⋆-contr p })
        , (λ p → by (ϕ→Realign p)) ⌟ᶠ)

    ⌞_⌟ᵉ : (a : A) → Elᶠ ⌞ A ⌟ᶠᶜ ⌞ (λ _ → a) ⌟
    ⌞ a ⌟ᵉ = glue (wrap ⌞ η⋆ (a , by (λ _ → refl)) ⌟ᴿ)

    ⌜_⌝ᵉ : Elᶠ ⌞ A ⌟ᶠᶜ aᵇ → A
    ⌜_⌝ᵉ {A = A} {aᵇ = aᵇ} a
      = elim⋆ (λ _ → A) proj₁ (⌜ aᵇ ⌝) (λ p (a , by prf) → dep (sym (prf p)))
        (⌜ unwrap (unglue a) ⌝ᴿ) 

    ⌜⌞⌟ᵉ⌝ᵉ : (a : A) → ⌜ ⌞ a ⌟ᵉ ⌝ᵉ ≡ a
    ⌜⌞⌟ᵉ⌝ᵉ a = refl

  {-# REWRITE ⌜⌞⌟ᵉ⌝ᵉ #-}

  -- The total space of a total-fracture of a prop is a prop.
  opaque
    unfolding Setᶠ Elᶠ Glue ⌞_⌟ᶠ ⌜_⌝ᶠ ⌞_⌟ᶠᶜ

    ⌞⌟ᶠᶜ-tot-prop : (A-prop : ∀ (x y : A) → x ≡ y)
      → (s t : Σ[ aᵇ ∈ Elᵇ ⌞ (λ _ → A) ⌟ᵇ ] (Elᶠ ⌞ A ⌟ᶠᶜ aᵇ))
      → s ≡ t
    ⌞⌟ᶠᶜ-tot-prop {A = A} A-prop (a , x) (b , y) =
      Σ≡ (⌞⌟ᵇ-prop A-prop a b) (inj-Realign (⋆-prop Σ-prop
        ⌜ subst (Elᶠ ⌞ A ⌟ᶠᶜ) (⌞⌟ᵇ-prop A-prop a b) x ⌝ᴿ ⌜ y ⌝ᴿ))
      where
        Σ-prop : (u v : Σ[ z ∈ A ] ((q : ϕ) → ⌜ b ⌝ q ≡ z) holds) → u ≡ v
        Σ-prop (z , by _) (z' , by _) = Σ≡ (A-prop z z') (true-prop _ _)

  -- Under ϕ every fiber is contractible, hence a prop.
  opaque
    unfolding Setᶠ Elᶠ coe ap-Elᶠᵇ
    ϕ-fiber-prop : (p : ϕ) (e : aᵇ ≡ bᵇ) (x : Elᶠ Aᶠ aᵇ) (y : Elᶠ Aᶠ bᵇ) → x ≡[ ap-Elᶠᵇ e ] y
    ϕ-fiber-prop {Aᶠ = Aᶠ} p refl x y = contr (⌜ Aᶠ ⌝ᴿ _ .proj₂ p) x y

  -- Russell fiber universe
  opaque
    unfolding Setᶠ Elᶠ

    Uᶠ : Setᶠ {ℓ = lsuc ℓ} (Uᵇ ℓ)
    Uᶠ {ℓ = ℓ} = ⌞ (λ Aᵇ → Setᶠ Aᵇ , (λ p → by (ϕ→Realign p))) ⌟ᴿ

    russellᶠ : ∀ {Aᵇ : Setᵇ tt𝟙 ℓ} → Setᶠ Aᵇ ≡ Elᶠ Uᶠ Aᵇ
    russellᶠ = refl

  {-# REWRITE russellᶠ #-}

  -- Booleans
  opaque
    unfolding 𝟚ᵇ trueᵇ falseᵇ ⌞_⌟ᶠᶜ ⌞_⌟ᵉ coe

    𝟚ᶠ : Setᶠ {ℓ = ℓ} 𝟚ᵇ
    𝟚ᶠ {ℓ = ℓ} = ⌞ Lift ℓ Bool ⌟ᶠᶜ

    trueᶠ : Elᶠ {Aᵇ = 𝟚ᵇ {ℓ = ℓ}} 𝟚ᶠ trueᵇ
    trueᶠ = ⌞ lift Bool.true ⌟ᵉ

    falseᶠ : Elᶠ {Aᵇ = 𝟚ᵇ {ℓ = ℓ}} 𝟚ᶠ falseᵇ
    falseᶠ = ⌞ lift Bool.false ⌟ᵉ

    ifᶠ_ret_then_else_ : ∀ {ℓ ℓ' Fᵇ aᵇ bᵇ cᵇ}
      → (x : Elᶠ {ℓ = ℓ} 𝟚ᶠ aᵇ)
      → (P : ∀ {aᵇ} → Elᶠ {ℓ = ℓ} 𝟚ᶠ aᵇ → Setᶠ {ℓ = ℓ'} (Fᵇ aᵇ))
      → Elᶠ (P trueᶠ) bᵇ → Elᶠ (P falseᶠ) cᵇ
      → Elᶠ (P x) (ifᵇ aᵇ ret Fᵇ then bᵇ else cᵇ)
    ifᶠ_ret_then_else_ {ℓ = ℓ} {ℓ' = ℓ'} {Fᵇ = Fᵇ} {aᵇ = aᵇ} {bᵇ = bᵇ} {cᵇ = cᵇ} x P t f =
      into (elim⋆
        (λ y → ⌜ Ext (P (glue (wrap ⌞ y ⌟ᴿ))) (ifᵇ aᵇ ret Fᵇ then bᵇ else cᵇ) ⌝ᶠ .proj₁)
        (λ { (lift Bool.true , by eq) →
               out (coe (cong (M (lift Bool.true)) (Σ≡ (sym (cong ⌞_⌟ (propfunext eq))) refl)) t)
           ; (lift Bool.false , by eq) →
               out (coe (cong (M (lift Bool.false)) (Σ≡ (sym (cong ⌞_⌟ (propfunext eq))) refl)) f) })
        (λ p → pt (⌜ Ext (P (glue (wrap ⌞ ϕ-pt⋆ p ⌟ᴿ))) (ifᵇ aᵇ ret Fᵇ then bᵇ else cᵇ) ⌝ᶠ .proj₂ p))
        (λ p _ → contr (⌜ Ext (P (glue (wrap ⌞ ϕ-pt⋆ p ⌟ᴿ))) (ifᵇ aᵇ ret Fᵇ then bᵇ else cᵇ) ⌝ᶠ .proj₂ p) _ _)
        (⌜ unwrap (unglue x) ⌝ᴿ))
      where
        M : (v : Lift ℓ Bool) → Σ[ z ∈ Elᵇ 𝟚ᵇ ] ((q : ϕ) → ⌜ z ⌝ q ≡ v) holds → Set ℓ'
        M v zp = Elᶠ (P (glue (wrap ⌞ η⋆ (v , zp .proj₂) ⌟ᴿ))) (ifᵇ zp .proj₁ ret Fᵇ then bᵇ else cᵇ)

    ifᶠtrue : ∀ {ℓ ℓ'} {Fᵇ : Elᵇ (𝟚ᵇ {ℓ = ℓ}) → Setᵇ tt𝟙 ℓ'}
        {P : ∀ {aᵇ} → Elᶠ {ℓ = ℓ} 𝟚ᶠ aᵇ → Setᶠ {ℓ = ℓ'} (Fᵇ aᵇ)}
        {bᵇ : Elᵇ (Fᵇ trueᵇ)} {cᵇ : Elᵇ (Fᵇ falseᵇ)}
        {t : Elᶠ (P trueᶠ) bᵇ} {f : Elᶠ (P falseᶠ) cᵇ}
        → (ifᶠ trueᶠ ret P then t else f) ≡ t
    ifᶠtrue = refl

    ifᶠfalse : ∀ {ℓ} {Fᵇ : Elᵇ (𝟚ᵇ {ℓ = ℓ}) → Setᵇ tt𝟙 ℓ'}
        {P : ∀ {aᵇ} → Elᶠ {ℓ = ℓ} 𝟚ᶠ aᵇ → Setᶠ {ℓ = ℓ'} (Fᵇ aᵇ)}
        {bᵇ : Elᵇ (Fᵇ trueᵇ)} {cᵇ : Elᵇ (Fᵇ falseᵇ)}
        {t : Elᶠ (P trueᶠ) bᵇ} {f : Elᶠ (P falseᶠ) cᵇ}
        → (ifᶠ falseᶠ ret P then t else f) ≡ f
    ifᶠfalse = refl

  {-# REWRITE ifᶠtrue ifᶠfalse #-}

  ifᶠ_then_else : Elᶠ (𝟚ᶠ {ℓ = ℓ}) aᵇ → Elᶠ Aᶠ bᵇ → Elᶠ Aᶠ cᵇ → Elᶠ Aᶠ (ifᵇ aᵇ then bᵇ else cᵇ)
  ifᶠ_then_else {Aᶠ = Aᶠ} x a b = ifᶠ x ret (λ _ → Aᶠ) then a else b
