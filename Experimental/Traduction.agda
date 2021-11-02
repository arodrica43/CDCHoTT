{-# OPTIONS --without-K --cubical #-}

module CDCHoTT.Experimental.Traduction where

  open import CDCHoTT.Basics
  open import CDCHoTT.EqualityAndPaths renaming (refl to refl' ; transport to ptransp ; _•_ to _∙̂_)
  open import CDCHoTT.Cubical.Core
  open import Cubical.Foundations.Everything


  𝟙-contraction' : (x : 𝟙) → x ≡ ∗
  𝟙-contraction' ∗ = refl
  
  ptransp' : ∀ {i j} {A : U i}  {x y : A} → (P : A → U j) → (γ : x ≡ y) → (P x → P y)
  ptransp' P p = ptransp P (≡-is-≈ p)
  
  apd' : ∀ {i j} {A : U j} {x y : A} → (P : A → U i) → (s : (a : A) → P a) → (γ : x ≡ y) → (ptransp' P γ (s x) ≡ s y)
  apd' P s p = ≈-is-≡ (apd P s (≡-is-≈ p))
  
  refl-is-right-neutral' : ∀ {i} {A : U i} {x y : A} (p : x ≡ y) → p ≡ p ∙ refl
  refl-is-right-neutral' p = {!!}
  
  --refl-is-left-neutral' : ∀ {i} {A : U i} {x y : A} (γ : x ≈ y) → γ ≈ refl • γ
  --refl-is-left-neutral' refl = refl
  
