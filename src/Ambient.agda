module Ambient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Data.Unit
open import Agda.Primitive


-- We need to postulate open/closed modalities somehow Let's just model the
-- topos Set↓Γ. This is the comma category X → Γ Y where X is a set and Y is a
-- presheaf over the syntax

record _true (P : Prop) : Type where
  constructor [_]
  field
    fact : P

module Set↓Γ where

  postulate
    ¶ : Prop
    
  variable
    i : Level
    X Y : Type i
    
  ◯ : Type i → Type i
  ◯ X = {{_ : ¶}} → X

  data ● (X : Type i) : Type i where
    * : {{_ : ¶}} → ● X
    η : X → ● X
    trivial : {{p : ¶}} {x : X} → * ≡ η x
  
  *-collapses : {{_ : ¶}} {y : ● X} → * ≡ y
  *-collapses {y = *} = refl
  *-collapses {y = η x} = trivial
  *-collapses {y = trivial {x = x} i} j = trivial {x = x} (i ∧ j)
  
  ●◯-trivial : ◯ (● X) ≃ ⊤
  ●◯-trivial .fst x = tt
  ●◯-trivial .snd .equiv-proof tt = (* , refl) , λ (y , p) i → *-collapses {y = y} i , refl
  
  record ●-Modal (X : Type i) : Type i where
    no-eta-equality
    field
      prf : isEquiv {A = ¶ true × X} {B = ¶ true} (λ (p , _) → p)
  
  record ◯-Modal (X : Type i) : Type i where
    no-eta-equality
    field
      prf : isEquiv {A = X} {B = {{_ : ¶}} → X} (λ x → x)
  
  -- ◯-fn-iso : (◯Y : ◯-Modal Y) → isEquiv {A = ◯ X → Y} {B = X → Y} (λ f x → f x)
  -- ◯-fn-iso ◯Y .equiv-proof f
  --   = ((λ x → invIsEq ◯Y (f x)) , λ i x → retIsEq ◯Y (f x) i) , {!   !}
      -- , (λ (p , q) i → (λ x → {!   !}) , {!   !})
  
  ◯ᴰ : ◯ (Type i) → Type i
  ◯ᴰ A = {{_ : ¶}} → A

  [_∣_↪_] : (A : Type i) → (P : Prop) → ({{_ : P}} → A) → Type i
  [ X ∣ P ↪ x ] = Σ[ a ∈ X ] ({{_ : P}} → a ≡ x)
  
  give : ∀ {P} {{_ : P}} A → (X : [ Type i ∣ P ↪ A ]) → A → X .fst
  give _ (X , p) a = transport (sym p) a
  
  give' : ∀ {P} {{_ : P}} A → (X : [ Type i ∣ P ↪ A ]) → X .fst → A
  give' _ (X , p) a = transport p a

  G : (A : ◯ (Type i))
    → (B : ◯ᴰ A → Type i)
    → {{B● : ∀ {a : ◯ᴰ A} → ●-Modal (B a)}}
    → Type i
  G A B = Σ[ a ∈ ◯ᴰ A ] B a
  
  syntax G A (λ x → B) = G[ x ∈ A ] B
  
  G-collapses : ∀ {{_ : ¶}} (A : ◯ (Type i)) (B : ◯ᴰ A → Type i)
    {{B● : ∀ {a : ◯ᴰ A} → ●-Modal (B a)}} → G[ a ∈ A ] B a ≡ A
  G-collapses A B = (λ i → G A λ a → {!  ua  !}) ∙' {!   !}

  
  instance
    [_∣¶↪_]-is-●-Modal : {A : Type i} → {x : ◯ A} → ●-Modal [ A ∣ ¶ ↪ x ]
  
  
module LF where
  open Set↓Γ

  record STLC i : Type (lsuc i) where
    field
      Ty : Type (lsuc i)
      Tm : Ty → Type i

      _⇒_ : Ty → Ty → Ty
      lam : ∀ {A B} → (Tm A → Tm B) → Tm (A ⇒ B)
      app : ∀ {A B} → Tm (A ⇒ B) → Tm A → Tm B
      ⇒-β : ∀ {A B} (f : Tm A → Tm B) (x : Tm A) → app (lam f) x ≡ f x
      ⇒-η : ∀ {A B} (f : Tm (A ⇒ B)) → lam (λ x → app f x) ≡ f

      _×'_ : Ty → Ty → Ty
      pair : ∀ {A B} → Tm A → Tm B → Tm (A ×' B)
      fst : ∀ {A B} → Tm (A ×' B) → Tm A
      snd : ∀ {A B} → Tm (A ×' B) → Tm B
      ×'-β-fst : ∀ {A B} (p : Tm A) (q : Tm B) → fst (pair p q) ≡ p
      ×'-β-snd : ∀ {A B} (p : Tm A) (q : Tm B) → snd (pair p q) ≡ q
      ×'-η : ∀ {A B} (p : Tm (A ×' B)) → pair (fst p) (snd p) ≡ p

  postulate
    S : ∀ {i} → ◯ (STLC i)

  open STLC

  C : [ STLC (lsuc lzero) ∣ ¶ ↪ S ]

  C .fst .Ty = G[ A ∈ S .Ty ] [ Type1 ∣ ¶ ↪ S .Tm A ]
  C .fst .Tm A = A .snd .fst
  C .fst ._⇒_ A B
    = S ._⇒_ (A .fst) (B .fst) ,
      (G[ f ∈  S .Tm (S ._⇒_ (A .fst) (B .fst)) ]
        [ (A .snd .fst → B .snd .fst)
          ∣ ¶ ↪ (λ a → give (S .Tm (B .fst)) (B .snd) (S .app f (give' (S .Tm (A .fst)) (A .snd) a))) ]
      , G-collapses _ _)
  C .fst .lam = {!   !}
  C .fst .app = {!   !}
  C .fst .⇒-β = {!   !}
  C .fst .⇒-η = {!   !}
  C .fst ._×'_ = {!   !}
  C .fst .pair = {!   !}
  C .fst .fst = {!   !}
  C .fst .snd = {!   !}
  C .fst .×'-β-fst = {!   !}
  C .fst .×'-β-snd = {!   !}
  C .fst .×'-η = {!   !}

  C .snd i .Ty = G-collapses _ _ i
  C .snd i .Tm A = {!   !}
  C .snd i ._⇒_ = {!   !}
  C .snd i .lam = {!   !}
  C .snd i .app = {!   !}
  C .snd i .⇒-β = {!   !}
  C .snd i .⇒-η = {!   !}
  C .snd i ._×'_ = {!   !}
  C .snd i .pair = {!   !}
  C .snd i .fst = {!   !}
  C .snd i .snd = {!   !}
  C .snd i .×'-β-fst = {!   !}
  C .snd i .×'-β-snd = {!   !}
  C .snd i .×'-η = {!   !}