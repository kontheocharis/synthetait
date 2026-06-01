module Realignment where

open import Agda.Primitive
open import Data.Product
open import Utils

record Isomorph {ℓ} (A : Set ℓ) : Set (lsuc ℓ) where
  field
    [_] : Set ℓ
    iso : A ≃ [_]

open Isomorph public

private variable
  ℓ ℓ' : Level
  ϕ : Prop ℓ'
  A : Set ℓ
  I I' : Isomorph _

-- For any proposition ϕ, any set A, and any ϕ-partial isomorph of A, we can
-- produce a single isomorph A' of A that agrees with the partial isomorph
-- strictly.
postulate
  realign : (A : Set ℓ) (B : ϕ → Isomorph A)
          → Σ[ A' ∈ Isomorph A ] ((p : ϕ) → (A' ≡ B p) true)

private variable
  B : ϕ → Isomorph A
  a : A

-- The realigned set.
opaque
  Realign : (ϕ : Prop ℓ') (A : Set ℓ) → (ϕ → Isomorph A) → Set ℓ
  Realign _ A B = [ realign A B .proj₁ ]

  ⌞_⌟ : A → Realign ϕ A B
  ⌞_⌟ a = realign _ _ .proj₁ .iso .to a

  ⌜_⌝ : Realign ϕ A B → A
  ⌜_⌝ x = realign _ _ .proj₁ .iso .from x

  ⌜⌞⌟ : ⌜ ⌞_⌟ {B = B} a ⌝ ≡ a
  ⌜⌞⌟ = realign _ _ .proj₁ .iso .from-to _

  ⌞⌜⌝ : ⌞ ⌜ a ⌝ ⌟ ≡ a
  ⌞⌜⌝ = realign _ _ .proj₁ .iso .to-from _

  ϕ→Iso : (p : ϕ) → realign A B .proj₁ ≡ B p
  ϕ→Iso {B = B} p = realign _ B .proj₂ p .witness

  ϕ→Realign : (p : ϕ) → Realign ϕ A B ≡ [ B p ]
  ϕ→Realign p = cong [_] (ϕ→Iso p)

{-# REWRITE ⌜⌞⌟ ⌞⌜⌝ #-}

opaque
  unfolding ⌞_⌟ ⌜_⌝ coe

  ϕ→⌞⌟ : (p : ϕ) → ⌞_⌟ {B = B} a ≡[ ϕ→Realign p ] B p .iso .to a
  ϕ→⌞⌟ {B = B} {a} p = aux (ϕ→Iso {B = B} p)
    where
      aux : (q : I ≡ I') → I .iso .to a ≡[ cong [_] q ] I' .iso .to a
      aux refl = refl

  ϕ→⌜⌝ : (p : ϕ) → ⌜_⌝ {B = B} a ≡ B p .iso .from (coe (ϕ→Realign p) a)
  ϕ→⌜⌝ {B = B} {x} p = aux (ϕ→Iso p) x
    where
      aux : (q : I ≡ I') (y : [ I ]) → I .iso .from y ≡ I' .iso .from (coe (cong [_] q) y)
      aux refl y = refl
