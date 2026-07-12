module STLC where

open import Agda.Primitive
open import Utils
open import Data.Product
open import Data.Unit using () renaming (⊤ to 𝟙; tt to tt𝟙)
import Gluing.Unary as Unary

-- Here we construct a canonicity model for STLC.
--
-- The intended interpretation for canonicity is:
-- Given T : 1 → C picking the terminal object ∙ of the STLC syntactic category,
-- construct the glued presheaf topos Gl(T*) where T* : Psh C → Set. Its objects
-- are (Γᵇ : Psh C , Γᶠ : Γᵇ ∙ → Set). It has a proposition # = (⊤ , λ tt → ⊥).
--
-- The base of the type theory is modelled by the Psh C, and the fibers are
-- modelled by the projection Gl(T*) → Psh C. As a result, the base is
-- open-modal (weakening by # is an iso) and the fibers are closed modal
-- (contractible under #). A total type (Aᵇ : Setᵇ tt𝟙 ℓ , Aᶠ : Setᶠ Aᵇ) is
-- essentially a fractured type in Gl(T*).

module In (ϕ : Prop) where
  open Unary.In ϕ

  variable ℓ : Level

  -- We define a notion of second-order model for STLC in the base, as well as
  -- its aligned version in the fibers.

  record STLCˢ : Set (lsuc (lsuc ℓ)) where
    field
      ty : Setᵇ tt𝟙 (lsuc ℓ)
      tm : Elᵇ ty → Setᵇ tt𝟙 ℓ

  module in-STLCˢ {ℓ} (s : STLCˢ {ℓ}) where
    open STLCˢ s

    variable
      α β : Elᵇ ty
      f g : Elᵇ (tm α) → Elᵇ (tm β)
      t u : Elᵇ (tm α)

    record STLCᶜ : Set (lsuc ℓ) where
      field
        _⇒_ : Elᵇ ty → Elᵇ ty → Elᵇ ty
        lam : (Elᵇ (tm α) → Elᵇ (tm β)) → Elᵇ (tm (α ⇒ β))
        app : Elᵇ (tm (α ⇒ β)) → Elᵇ (tm α) → Elᵇ (tm β)
        ⇒β : app (lam f) u ≡ f u

        ans : Elᵇ ty
        yes : Elᵇ (tm ans)
        no : Elᵇ (tm ans)

  record STLC : Set (lsuc (lsuc ℓ)) where
    field
      ˢ : STLCˢ {ℓ}
    open STLCˢ ˢ public
    open in-STLCˢ ˢ public
    field
      ᶜ : STLCᶜ
    open STLCᶜ ᶜ public

  module in-STLC {ℓ} (s : STLC {ℓ}) where
    open STLC s

    -- We would ideally have
    -- STLC : Setᵇ tt𝟙 ℓ
    -- STLCᴰ : Setᶠ STLC
    -- to ensure that the fibers are properly aligned over the base.
    -- However, this would prevent us from using Agda records.

    record STLCᴰˢ : Set (lsuc (lsuc ℓ)) where
      field
        tyᴰ : Setᶠ ty
        tmᴰ : Elᶠ tyᴰ α → Setᶠ (tm α)

    module in-STLCᴰˢ (sᴰ : STLCᴰˢ) where
      open STLCᴰˢ sᴰ public

      variable
        αᴰ βᴰ : Elᶠ tyᴰ α
        fᴰ gᴰ : ∀ {t} → Elᶠ (tmᴰ αᴰ) t → Elᶠ (tmᴰ βᴰ) (f t)
        tᴰ uᴰ : Elᶠ (tmᴰ αᴰ) t

      record STLCᴰᶜ : Set (lsuc ℓ) where
        field
          _⇒ᴰ_ : Elᶠ tyᴰ α → Elᶠ tyᴰ β → Elᶠ tyᴰ (α ⇒ β)
          lamᴰ : (∀ {t} → Elᶠ (tmᴰ αᴰ) t → Elᶠ (tmᴰ βᴰ) (f t)) → Elᶠ (tmᴰ (αᴰ ⇒ᴰ βᴰ)) (lam f)
          appᴰ : Elᶠ (tmᴰ (αᴰ ⇒ᴰ βᴰ)) t → Elᶠ (tmᴰ αᴰ) u → Elᶠ (tmᴰ βᴰ) (app t u)
          ⇒βᴰ : appᴰ (lamᴰ fᴰ) uᴰ ≡[ ap-Elᶠᵇ ⇒β ] fᴰ uᴰ

          ansᴰ : Elᶠ tyᴰ ans
          yesᴰ : Elᶠ (tmᴰ ansᴰ) yes
          noᴰ : Elᶠ (tmᴰ ansᴰ) no

    record STLCᴰ : Set (lsuc (lsuc ℓ)) where
      field
        ᴰˢ : STLCᴰˢ
      open STLCᴰˢ ᴰˢ public
      open in-STLCᴰˢ ᴰˢ public
      field
        ᴰᶜ : STLCᴰᶜ
      open STLCᴰᶜ ᴰᶜ public

  -- There is a second-order model of STLC in Psh C because C is the syntactic
  -- category of contexts of STLC.
  module _ {ℓ : Level} where
    postulate
      syn : STLC {ℓ}

    open STLC syn
    open in-STLC
    open STLCᴰ
    open STLCᴰˢ
    open STLCᴰᶜ

    -- Build a model of STLC in Gl(T*) which restricts to syn in the base.
    canon : STLCᴰ syn
    canon .ᴰˢ .tyᴰ = G[ A ∈ ty ] [ Uᶠ ↪ tm A ]
    canon .ᴰˢ .tmᴰ A = ∣ A ∣
    canon .ᴰᶜ ._⇒ᴰ_ {α} {β} αᴰ βᴰ
      = ⟨ G[ f ∈ tm (α ⇒ β) ] [ ([ x ∈ᶠ ∣ αᴰ ∣ ] ⇒ ∣ βᴰ ∣) ↪ (λᵇ x ⇒ app f x) ] ⟩
    canon .ᴰᶜ .lamᴰ f = ⟨ λᶠ x ⇒ coe (ap-Elᶠᵇ (sym ⇒β)) (f x) ⟩
    canon .ᴰᶜ .appᴰ t u = ∣ t ∣ ∙ᶠ u
    canon .ᴰᶜ .⇒βᴰ = splitl reflᴰ
    canon .ᴰᶜ .ansᴰ = ⟨ G[ a ∈ tm ans ] (● ([ b ∈ᶠ 𝟚ᶠ {ℓ} ] × ifᶠ b ret (λ _ → Uᶠ {ℓ}) then (○ (a ≡ᵇ yes)) else (○ (a ≡ᵇ no)))) ⟩
    canon .ᴰᶜ .yesᴰ = glue (η● (pairᶠ trueᶠ (η○ rflᵇ)))
    canon .ᴰᶜ .noᴰ = glue (η● (pairᶠ falseᶠ (η○ rflᵇ)))

    -- By usual STC arguments, canon has a section
