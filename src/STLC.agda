module STLC where

open import Utils
open import Data.Product
open import LF

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
-- (contractible under #). A total type (Aᵇ : Tyᵇ , Aᶠ : Tyᶠ Aᵇ) is essentially a
-- fractured type in Gl(T*).

-- We define a notion of second-order model for STLC in the base, as well as
-- its aligned version in the fibers.

record STLCˢ : Set where
  field
    ty : Tyᵇ
    tm : Tmᵇ ty → Tyᵇ

module in-STLCˢ (s : STLCˢ) where
  open STLCˢ s

  variable
    α β : Tmᵇ ty
    f g : Tmᵇ (tm α) → Tmᵇ (tm β)
    t u : Tmᵇ (tm α)

  record STLCᶜ : Set where
    field
      _⇒_ : Tmᵇ ty → Tmᵇ ty → Tmᵇ ty
      lam : (Tmᵇ (tm α) → Tmᵇ (tm β)) → Tmᵇ (tm (α ⇒ β))
      app : Tmᵇ (tm (α ⇒ β)) → Tmᵇ (tm α) → Tmᵇ (tm β)
      ⇒β : app (lam f) u ≡ f u

      ans : Tmᵇ ty
      yes : Tmᵇ (tm ans)
      no : Tmᵇ (tm ans)

record STLC : Set where
  field
    ˢ : STLCˢ
  open STLCˢ ˢ public
  open in-STLCˢ ˢ public
  field
    ᶜ : STLCᶜ
  open STLCᶜ ᶜ public

module in-STLC (s : STLC) where
  open STLC s

  -- We would ideally have
  -- STLC : Tyᵇ
  -- STLCᴰ : Tyᶠ STLC
  -- to ensure that the fibers are properly aligned over the base.
  -- However, this would prevent us from using Agda records.

  record STLCᴰˢ : Set where
    field
      tyᴰ : Tyᶠ ty
      tmᴰ : Tmᶠ tyᴰ α → Tyᶠ (tm α)

  module in-STLCᴰˢ (sᴰ : STLCᴰˢ) where
    open STLCᴰˢ sᴰ public

    variable
      αᴰ βᴰ : Tmᶠ tyᴰ α
      fᴰ gᴰ : ∀ {t} → Tmᶠ (tmᴰ αᴰ) t → Tmᶠ (tmᴰ βᴰ) (f t)
      tᴰ uᴰ : Tmᶠ (tmᴰ αᴰ) t

    record STLCᴰᶜ : Set where
      field
        _⇒ᴰ_ : Tmᶠ tyᴰ α → Tmᶠ tyᴰ β → Tmᶠ tyᴰ (α ⇒ β)
        lamᴰ : (∀ {t} → Tmᶠ (tmᴰ αᴰ) t → Tmᶠ (tmᴰ βᴰ) (f t)) → Tmᶠ (tmᴰ (αᴰ ⇒ᴰ βᴰ)) (lam f)
        appᴰ : Tmᶠ (tmᴰ (αᴰ ⇒ᴰ βᴰ)) t → Tmᶠ (tmᴰ αᴰ) u → Tmᶠ (tmᴰ βᴰ) (app t u)
        ⇒βᴰ : appᴰ (lamᴰ fᴰ) uᴰ ≡[ ap-Tmᶠᵇ ⇒β ] fᴰ uᴰ

        ansᴰ : Tmᶠ tyᴰ ans
        yesᴰ : Tmᶠ (tmᴰ ansᴰ) yes
        noᴰ : Tmᶠ (tmᴰ ansᴰ) no

  record STLCᴰ : Set where
    field
      ᴰˢ : STLCᴰˢ
    open STLCᴰˢ ᴰˢ public
    open in-STLCᴰˢ ᴰˢ public
    field
      ᴰᶜ : STLCᴰᶜ
    open STLCᴰᶜ ᴰᶜ public


-- There is a second-order model of STLC in Psh C because C is the syntactic
-- category of contexts of STLC.
postulate
  syn : STLC

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
canon .ᴰᶜ .lamᴰ f = ⟨ λᶠ x ⇒ coe (ap-Tmᶠᵇ (sym ⇒β)) (f x) ⟩
canon .ᴰᶜ .appᴰ t u = ∣ t ∣ ∙ᶠ u
canon .ᴰᶜ .⇒βᴰ = splitl reflᴰ
canon .ᴰᶜ .ansᴰ = ⟨ G[ a ∈ tm ans ] (● ([ b ∈ᶠ 𝟚ᶠ ] × ifᶠ b then (○ (a ≡ᵇ yes)) else (○ (a ≡ᵇ no)))) ⟩
canon .ᴰᶜ .yesᴰ = glue (η● (pairᶠ trueᶠ (η○ rflᵇ))) 
canon .ᴰᶜ .noᴰ = glue (η● (pairᶠ falseᶠ (η○ rflᵇ))) 

-- By usual STC arguments, canon has a section
