module LF where

open import Utils
open import Data.Product

-- We work internally to an indexed type theory.
-- Its models are displayed models of type theory (equivalently morphisms of
-- models of type theory) that support certain presheaf type formers.
-- The intended interpretation is a glued category; STLC.agda for an example.
--
-- We ignore size issues for now..

-- Base
postulate
  Tyᵇ : Set
  Tmᵇ : Tyᵇ → Set

variable
  Aᵇ Bᵇ Cᵇ : Tyᵇ
  Fᵇ Gᵇ Hᵇ : Tmᵇ Aᵇ → Tyᵇ
  aᵇ bᵇ cᵇ : Tmᵇ Aᵇ
  fᵇ gᵇ hᵇ : (xᵇ : Tmᵇ Aᵇ) → Tmᵇ (Fᵇ xᵇ)

-- Base type formers
postulate
  Πᵇ : (Aᵇ : Tyᵇ) → (Tmᵇ Aᵇ → Tyᵇ) → Tyᵇ
  lamᵇ : ((xᵇ : Tmᵇ Aᵇ) → Tmᵇ (Fᵇ xᵇ)) → Tmᵇ (Πᵇ Aᵇ Fᵇ)
  appᵇ : Tmᵇ (Πᵇ Aᵇ Fᵇ) → (xᵇ : Tmᵇ Aᵇ) → Tmᵇ (Fᵇ xᵇ)
  Πηᵇ : lamᵇ (appᵇ aᵇ) ≡ aᵇ
  Πβᵇ : appᵇ (lamᵇ fᵇ) aᵇ ≡ fᵇ aᵇ
  {-# REWRITE Πηᵇ Πβᵇ #-}

  Σᵇ : (Aᵇ : Tyᵇ) → (Tmᵇ Aᵇ → Tyᵇ) → Tyᵇ
  pairᵇ : (xᵇ : Tmᵇ Aᵇ) → Tmᵇ (Fᵇ xᵇ) → Tmᵇ (Σᵇ Aᵇ Fᵇ)
  fstᵇ : Tmᵇ (Σᵇ Aᵇ Fᵇ) → Tmᵇ Aᵇ
  sndᵇ : (p : Tmᵇ (Σᵇ Aᵇ Fᵇ)) → Tmᵇ (Fᵇ (fstᵇ p))
  Σfstᵇ : fstᵇ (pairᵇ aᵇ bᵇ) ≡ aᵇ
  {-# REWRITE Σfstᵇ #-}
  Σsndᵇ : sndᵇ (pairᵇ aᵇ bᵇ) ≡ bᵇ
  {-# REWRITE Σsndᵇ #-}
  Σηᵇ : pairᵇ (fstᵇ aᵇ) (sndᵇ aᵇ) ≡ aᵇ
  {-# REWRITE Σηᵇ #-}

  Uᵇ : Tyᵇ
  russellᵇ : Tyᵇ ≡ Tmᵇ Uᵇ
  {-# REWRITE russellᵇ #-}

  𝟚ᵇ : Tyᵇ
  trueᵇ falseᵇ : Tmᵇ 𝟚ᵇ
  ifᵇ_ret_then_else_ : (x : Tmᵇ 𝟚ᵇ) → (P : Tmᵇ 𝟚ᵇ → Tyᵇ) → Tmᵇ (P trueᵇ) → Tmᵇ (P falseᵇ) → Tmᵇ (P x)
  ifᵇtrue : ifᵇ trueᵇ ret Fᵇ then aᵇ else bᵇ ≡ aᵇ
  ifᵇfalse : ifᵇ falseᵇ ret Fᵇ then aᵇ else bᵇ ≡ bᵇ
  {-# REWRITE ifᵇtrue ifᵇfalse #-}

ifᵇ_then_else : Tmᵇ 𝟚ᵇ → Tmᵇ Aᵇ → Tmᵇ Aᵇ → Tmᵇ Aᵇ
ifᵇ_then_else {Aᵇ} x a b = ifᵇ x ret (λ _ → Aᵇ) then a else b

postulate
  _≡ᵇ_ : Tmᵇ Aᵇ → Tmᵇ Aᵇ → Tyᵇ
  rflᵇ : Tmᵇ (aᵇ ≡ᵇ aᵇ)
  reflectᵇ : Tmᵇ (aᵇ ≡ᵇ bᵇ) → aᵇ ≡ bᵇ

postulate
  𝟙ᵇ : Tyᵇ
  ttᵇ : Tmᵇ 𝟙ᵇ
  𝟙ᵇη : aᵇ ≡ ttᵇ

syntax Πᵇ Aᵇ (λ a → Fᵇ) = [ a ∈ᵇ Aᵇ ] ⇒ Fᵇ
syntax lamᵇ (λ a → tᵇ) = λᵇ a ⇒ tᵇ
syntax appᵇ t u = t ∙ᵇ u
syntax Σᵇ Aᵇ (λ a → Fᵇ) = [ a ∈ᵇ Aᵇ ] × Fᵇ

-- Fibers
postulate
  Tyᶠ : Tyᵇ → Set
  Tmᶠ : ∀ {Aᵇ} → Tyᶠ Aᵇ → Tmᵇ Aᵇ → Set

variable
  Aᶠ Bᶠ Cᶠ : Tyᶠ Aᵇ
  Fᶠ Gᶠ Hᶠ : ∀ {xᵇ} → Tmᶠ Aᶠ xᵇ → Tyᶠ (Fᵇ xᵇ)
  aᶠ bᶠ cᶠ : Tmᶠ Aᶠ aᵇ
  fᶠ gᶠ hᶠ : ∀ {xᵇ} (xᶠ : Tmᶠ Aᶠ xᵇ) → Tmᶠ (Fᶠ xᶠ) (fᵇ xᵇ)

opaque
  unfolding coe

  ap-Tmᶠᵇ : aᵇ ≡ bᵇ → Tmᶠ Aᶠ aᵇ ≡ Tmᶠ Aᶠ bᵇ 
  ap-Tmᶠᵇ refl = refl

-- Fiber type formers, indexed over their base versions
postulate
  Πᶠ : (Aᶠ : Tyᶠ Aᵇ) → (∀ {xᵇ} → Tmᶠ Aᶠ xᵇ → Tyᶠ (Fᵇ xᵇ)) → Tyᶠ (Πᵇ Aᵇ Fᵇ)
  lamᶠ : (∀ {xᵇ} (xᶠ : Tmᶠ Aᶠ xᵇ) → Tmᶠ (Fᶠ xᶠ) (fᵇ xᵇ)) → Tmᶠ (Πᶠ Aᶠ Fᶠ) (lamᵇ fᵇ)
  appᶠ : Tmᶠ (Πᶠ Aᶠ Fᶠ) aᵇ → (bᶠ : Tmᶠ Aᶠ bᵇ) → Tmᶠ (Fᶠ bᶠ) (appᵇ aᵇ bᵇ)
  Πηᶠ : lamᶠ (appᶠ {Fᶠ = Fᶠ} {aᵇ = aᵇ} aᶠ) ≡ aᶠ
  Πβᶠ : appᶠ (lamᶠ fᶠ) aᶠ ≡ fᶠ aᶠ
  {-# REWRITE Πηᶠ Πβᶠ #-}

  Σᶠ : (Aᶠ : Tyᶠ Aᵇ) → (∀ {xᵇ} → Tmᶠ Aᶠ xᵇ → Tyᶠ (Fᵇ xᵇ)) → Tyᶠ (Σᵇ Aᵇ Fᵇ)
  pairᶠ : (xᶠ : Tmᶠ Aᶠ aᵇ) → Tmᶠ (Fᶠ xᶠ) bᵇ → Tmᶠ (Σᶠ Aᶠ Fᶠ) (pairᵇ aᵇ bᵇ)
  fstᶠ : Tmᶠ (Σᶠ Aᶠ Fᶠ) aᵇ → Tmᶠ Aᶠ (fstᵇ aᵇ)
  sndᶠ : (p : Tmᶠ (Σᶠ Aᶠ Fᶠ) aᵇ) → Tmᶠ (Fᶠ (fstᶠ p)) (sndᵇ aᵇ)
  Σfstᶠ : fstᶠ (pairᶠ aᶠ bᶠ) ≡ aᶠ
  {-# REWRITE Σfstᶠ #-}
  Σsndᶠ : sndᶠ (pairᶠ aᶠ bᶠ) ≡ bᶠ
  {-# REWRITE Σsndᶠ #-}
  Σηᶠ : pairᶠ (fstᶠ aᶠ) (sndᶠ aᶠ) ≡ aᶠ
  {-# REWRITE Σηᶠ #-}

  Uᶠ : Tyᶠ Uᵇ
  russellᶠ : Tyᶠ Aᵇ ≡ Tmᶠ Uᶠ Aᵇ
  {-# REWRITE russellᶠ #-}

  𝟚ᶠ : Tyᶠ 𝟚ᵇ
  trueᶠ : Tmᶠ 𝟚ᶠ trueᵇ
  falseᶠ : Tmᶠ 𝟚ᶠ falseᵇ
  ifᶠ_ret_then_else_ : (x : Tmᶠ 𝟚ᶠ aᵇ)
    → (P : ∀ {aᵇ} → Tmᶠ 𝟚ᶠ aᵇ → Tyᶠ (Fᵇ aᵇ))
    → Tmᶠ (P trueᶠ) bᵇ → Tmᶠ (P falseᶠ) cᵇ
    → Tmᶠ (P x) (ifᵇ aᵇ ret Fᵇ then bᵇ else cᵇ)
  ifᶠtrue : ifᶠ trueᶠ ret Fᶠ then aᶠ else bᶠ ≡ aᶠ
  ifᶠfalse : ifᶠ falseᶠ ret Fᶠ then aᶠ else bᶠ ≡ bᶠ
  {-# REWRITE ifᶠtrue ifᶠfalse #-}

ifᶠ_then_else : Tmᶠ 𝟚ᶠ aᵇ → Tmᶠ Aᶠ bᵇ → Tmᶠ Aᶠ cᵇ → Tmᶠ Aᶠ (ifᵇ aᵇ then bᵇ else cᵇ)
ifᶠ_then_else {Aᶠ = Aᶠ} x a b = ifᶠ x ret (λ _ → Aᶠ) then a else b

syntax Πᶠ Aᶠ (λ a → Fᶠ) = [ a ∈ᶠ Aᶠ ] ⇒ Fᶠ
syntax lamᶠ (λ a → tᶠ) = λᶠ a ⇒ tᶠ
syntax appᶠ t u = t ∙ᶠ u
syntax Σᶠ Aᶠ (λ a → Fᶠ) = [ a ∈ᶠ Aᶠ ] × Fᶠ

-- Glue and extension types
variable
  Xᶠ : Tmᵇ Aᵇ → Tyᶠ 𝟙ᵇ
  Yᶠ : (aᵇ : Tmᵇ Aᵇ) → Tyᶠ (Fᵇ aᵇ)

postulate
  Ext : Tyᶠ Aᵇ → Tmᵇ Aᵇ → Tyᶠ 𝟙ᵇ
  ext : Tmᶠ Aᶠ aᵇ → Tmᶠ (Ext Aᶠ aᵇ) ttᵇ
  unext : Tmᶠ (Ext Aᶠ aᵇ) ttᵇ → Tmᶠ Aᶠ aᵇ
  ext-unext : ext (unext aᶠ) ≡ aᶠ
  unext-ext : unext (ext aᶠ) ≡ aᶠ
  {-# REWRITE ext-unext unext-ext #-}

  Glue : (Aᵇ : Tyᵇ) → (Tmᵇ Aᵇ → Tyᶠ 𝟙ᵇ) → Tyᶠ Aᵇ
  glue : Tmᶠ (Xᶠ aᵇ) bᵇ → Tmᶠ (Glue Aᵇ Xᶠ) aᵇ
  unglue : Tmᶠ (Glue Aᵇ Xᶠ) aᵇ → Tmᶠ (Xᶠ aᵇ) ttᵇ
  glue-unglue : glue (unglue aᶠ) ≡ aᶠ
  unglue-glue : unglue {Aᵇ = Aᵇ} (glue aᶠ) ≡ aᶠ
  {-# REWRITE glue-unglue unglue-glue #-}

syntax Ext Aᶠ aᵇ = [ Aᶠ ↪ aᵇ ]
syntax Glue Aᶠ (λ a → Xᵇ) = G[ a ∈ Aᶠ ] Xᵇ

∣_∣ : Tmᶠ (G[ x ∈ Aᵇ ] [ Yᶠ x ↪ fᵇ x ]) aᵇ → Tmᶠ (Yᶠ aᵇ) (fᵇ aᵇ)
∣ p ∣ = unext (unglue p)

⟨_⟩ : Tmᶠ (Yᶠ aᵇ) (fᵇ aᵇ) → Tmᶠ (G[ x ∈ Aᵇ ] [ Yᶠ x ↪ fᵇ x ]) aᵇ
⟨ p ⟩ = glue (ext p)

-- Closed modality
postulate
  ● : Tyᶠ Aᵇ → Tyᶠ 𝟙ᵇ
  η● : Tmᶠ Aᶠ aᵇ → Tmᶠ (● Aᶠ) ttᵇ
  elim-● : (Pᶠ : ∀ (x : Tmᶠ (● Aᶠ) ttᵇ) → Tyᶠ 𝟙ᵇ)
    → (η●ᴹ : ∀ {aᵇ} (aᶠ : Tmᶠ Aᶠ aᵇ) → Tmᶠ (Pᶠ (η● aᶠ)) ttᵇ)
    → ∀ aᶠ → Tmᶠ (Pᶠ aᶠ) ttᵇ
  elim-●-η● : ∀ Pᶠ (η●ᴹ : ∀ {aᵇ} (aᶠ : Tmᶠ Aᶠ aᵇ) → Tmᶠ (Pᶠ (η● aᶠ)) ttᵇ) aᵇ aᶠ
    → elim-● {Aᶠ = Aᶠ} Pᶠ η●ᴹ (η● {aᵇ = aᵇ} aᶠ) ≡ η●ᴹ aᶠ
  {-# REWRITE elim-●-η● #-}

_>>=_ : Tmᶠ (● Aᶠ) ttᵇ → (∀ {aᵇ} (aᶠ : Tmᶠ Aᶠ aᵇ) → Tmᶠ Bᶠ ttᵇ) → Tmᶠ Bᶠ ttᵇ
_>>=_ {Bᶠ = Bᶠ} x f = elim-● (λ _ → Bᶠ) f x

-- Open modality
postulate
  ○ : (Aᵇ : Tyᵇ) → Tyᶠ Aᵇ
  η○ : ∀ aᵇ → Tmᶠ (○ Aᵇ) aᵇ
  η○-contr : η○ aᵇ ≡ bᶠ




-- Iso up to a notion of iso
record _≃'_by_and_ (A : Set) (B : Set) (_≃A_ : A → A → Set) (_≃B_ : B → B → Set) : Set where
  field
    to : A → B
    from : B → A
    to-from : ∀ x → to (from x) ≃B x
    from-to : ∀ x → from (to x) ≃A x

open _≃'_by_and_

-- Glue and extension types exhibit the fact that the fibers are purely semantic
-- data indexed over purely base data.
fracture : Tyᶠ Aᵇ ≃' (Tmᵇ Aᵇ → Tyᶠ 𝟙ᵇ)
            by (λ A B → ∀ aᵇ → Tmᶠ A aᵇ ≃ Tmᶠ B aᵇ)
            and λ F G → ∀ aᵇ → Tmᶠ (F aᵇ) ttᵇ ≃ Tmᶠ (G aᵇ) ttᵇ
fracture .to = Ext
fracture .from = Glue _
fracture .to-from f aᵇ .to x = unglue (unext x)
fracture .to-from f aᵇ .from x = ext (glue x)
fracture .to-from f aᵇ .to-from x = refl
fracture .to-from f aᵇ .from-to x = refl
fracture .from-to g aᵇ .to x = unext (unglue x)
fracture .from-to g aᵇ .from x = glue (ext x)
fracture .from-to g aᵇ .to-from x = refl
fracture .from-to g aᵇ .from-to x = refl
