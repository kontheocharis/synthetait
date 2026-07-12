module Gluing.Realignment where

open import Agda.Primitive
open import Data.Product
open import Data.Unit using () renaming (⊤ to 𝟙; tt to tt𝟙)
open import Level using (Lift; lift)
open import Utils

record Isomorph {ℓ} (A : Set ℓ) : Set (lsuc ℓ) where
  field
    [_] : Set ℓ
    iso : A ≃ [_]

open Isomorph public

private variable
  ℓ ℓ' ℓ'' : Level
  ϕ : Prop
  A : Set ℓ
  I I' : Isomorph _

-- For any proposition ϕ, any set A, and any ϕ-partial family of isomorphs of A,
-- we can produce a single isomorph A' of A that agrees with the family strictly
-- under ϕ.
postulate
  realign : (A : Set ℓ) (B : ϕ → Isomorph A)
          → Σ[ A' ∈ Isomorph A ] ((p : ϕ) → (A' ≡ B p) holds)

private variable
  B : ϕ → Isomorph A
  a b : A

opaque
  Realign : (ϕ : Prop) (A : Set ℓ) → (ϕ → Isomorph A) → Set ℓ
  Realign _ A B = [ realign A B .proj₁ ]

  ⌞_⌟ᴿ : A → Realign ϕ A B
  ⌞_⌟ᴿ a = realign _ _ .proj₁ .iso .to a

  ⌜_⌝ᴿ : Realign ϕ A B → A
  ⌜_⌝ᴿ x = realign _ _ .proj₁ .iso .from x

  ⌜⌞⌟⌝ : ⌜ ⌞_⌟ᴿ {B = B} a ⌝ᴿ ≡ a
  ⌜⌞⌟⌝ = realign _ _ .proj₁ .iso .from-to _

  ⌞⌜⌝⌟ : ⌞ ⌜ a ⌝ᴿ ⌟ᴿ ≡ a
  ⌞⌜⌝⌟ = realign _ _ .proj₁ .iso .to-from _

  ϕ→Iso : (p : ϕ) → realign A B .proj₁ ≡ B p
  ϕ→Iso {B = B} p = realign _ B .proj₂ p .witness

  ϕ→Realign : (p : ϕ) → Realign ϕ A B ≡ [ B p ]
  ϕ→Realign p = cong [_] (ϕ→Iso p)

  inj-Realign : ⌜ a ⌝ᴿ ≡ ⌜ b ⌝ᴿ → a ≡ b
  inj-Realign {a = x} {b = y} p
    = trans (sym (⌞⌜⌝⌟ {a = x})) (trans (cong ⌞_⌟ᴿ p) (⌞⌜⌝⌟ {a = y}))

  {-# INJECTIVE ⌞_⌟ᴿ #-}
  {-# INJECTIVE ⌜_⌝ᴿ #-}

{-# REWRITE ⌜⌞⌟⌝ ⌞⌜⌝⌟ #-}

opaque
  unfolding ⌞_⌟ᴿ ⌜_⌝ᴿ coe

  ϕ→⌞⌟ : (p : ϕ) → ⌞_⌟ᴿ {B = B} a ≡[ ϕ→Realign p ] B p .iso .to a
  ϕ→⌞⌟ {B = B} {a} p = aux (ϕ→Iso {B = B} p)
    where
      aux : (q : I ≡ I') → I .iso .to a ≡[ cong [_] q ] I' .iso .to a
      aux refl = refl

  ϕ→⌜⌝ : (p : ϕ) → ⌜_⌝ᴿ {B = B} a ≡ B p .iso .from (coe (ϕ→Realign p) a)
  ϕ→⌜⌝ {B = B} {x} p = aux (ϕ→Iso p) x
    where
      aux : (q : I ≡ I') (y : [ I ]) → I .iso .from y ≡ I' .iso .from (coe (cong [_] q) y)
      aux refl y = refl

-- The join `ϕ ⋆ A` as a QIT
-- This is a container of A which collapses to a point under ϕ
postulate
  _⋆_ : (ϕ : Prop) (A : Set ℓ) → Set ℓ
  η⋆ : A → ϕ ⋆ A
  ϕ-pt⋆ : ϕ → ϕ ⋆ A
  collapse⋆ : (p : ϕ) (x : ϕ ⋆ A) → x ≡ ϕ-pt⋆ p

  elim⋆ : (C : _⋆_ {ℓ = ℓ} ϕ A → Set ℓ')
    → (cη : ∀ a → C (η⋆ a))
    → (cϕ : ∀ p → C (ϕ-pt⋆ p))
    → (ccoh : ∀ p a → cη a ≡[ cong C (collapse⋆ p (η⋆ a)) ] cϕ p)
    → ∀ x → C x

  elim⋆-η⋆ : ∀ {C cη cϕ ccoh a}
    → elim⋆ {ℓ} {ϕ} {A} {ℓ'} C cη cϕ ccoh (η⋆ a) ≡ cη a
  elim⋆-ϕ-pt⋆ : ∀ {C cη cϕ ccoh p}
    → elim⋆ {ℓ} {ϕ} {A} {ℓ'} C cη cϕ ccoh (ϕ-pt⋆ p) ≡ cϕ p

{-# REWRITE elim⋆-η⋆ elim⋆-ϕ-pt⋆ #-}

true-prop : ∀ {ℓ} {P : Prop ℓ} (x y : P holds) → x ≡ y
true-prop (by _) (by _) = refl

-- ⋆ preserves isProp
⋆-prop : (∀ (x y : A) → x ≡ y) → (a b : ϕ ⋆ A) → a ≡ b
⋆-prop {A = A} {ϕ = ϕ} A-prop a b =
  elim⋆ (λ a → (a ≡ b) holds)
    (λ x → elim⋆ (λ b → (η⋆ x ≡ b) holds)
        (λ y → by (cong η⋆ (A-prop x y)))
        (λ p → by (collapse⋆ p (η⋆ x)))
        (λ p y → true-prop _ _)
      b)
    (λ p → by (sym (collapse⋆ p b)))
    (λ p x → true-prop _ _)
    a .witness
