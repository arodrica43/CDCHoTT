{-# OPTIONS --without-K #-}

module FormalDisk where 
  open import Basics
  open import EqualityAndPaths
  open import Homotopies
  open import Language
  open import Equivalences
  open import CommonEquivalences  
  open import Im
  open import LeftInvertibleHspace
  open import DependentTypes
  open import Fiber
  open import Contractibility
  open import HomogeneousType


  _is-infinitesimally-close-to_ :
    {X : U₀} → (x x′ : X) → U₀
  x is-infinitesimally-close-to x′ = ℑ-unit x ≈ ℑ-unit x′

  -- shorthand
  _is-close-to_ :
    {X : U₀} → (x x′ : X) → U₀
  _is-close-to_ = _is-infinitesimally-close-to_


  -- since all maps preserve smooth structure,
  -- they also preserve infinitesimal proximity:
  
  mapping-with_preserves-infinitesimal-proximity :
    ∀ {X Y : U₀} {x x′ : X}
    → (f : X → Y)
    → (x is-close-to x′) → (f x) is-close-to (f x′)
  mapping-with f preserves-infinitesimal-proximity γ = ℑ⁎ f ⁎ γ  -- see 'Im.agda'
  

  -- T∞ as dependent type
  formal-disk-at_ :
    ∀ {X : U₀}
    → (x : X) → U₀
  formal-disk-at x = ∑ (λ x′ → x is-close-to x′)

  𝔻 :
    ∀ (X : U₀)
    → (x : X) → U₀
  𝔻 X x = formal-disk-at x
  
  inclusion-of-formal-disk-at :
    ∀ {X : U₀}
    → (x : X)
    → formal-disk-at x → X
  inclusion-of-formal-disk-at x (y , γ) = y

  ι-𝔻 = inclusion-of-formal-disk-at
  
  ∗-𝔻 :
    ∀ {X : 𝒰} {x : X}
    → 𝔻 X x
  ∗-𝔻 = (_ , refl)


  induced-map-on-formal-disks :
    ∀ {X Y : 𝒰}
    → (f : X → Y)
    → (x : X) → 𝔻 _ x → 𝔻 _ (f x)
  induced-map-on-formal-disks f x (x′ , x′-is-close-to-x) =
    (f x′ , mapping-with f preserves-infinitesimal-proximity x′-is-close-to-x)

  -- first order terminology
  push-forward : 
    ∀ {X Y : 𝒰}
    → (f : X → Y)
    → (x : X) → 𝔻 _ x → 𝔻 _ (f x)
  push-forward = induced-map-on-formal-disks
  
  -- the generalized differential of a function
  d :
    ∀ {X Y : 𝒰}
    → (f : X → Y)
    → (x : X) → 𝔻 _ x → 𝔻 _ (f x)
  d f x (x′ , x′-is-close-to-x) = induced-map-on-formal-disks f x (x′ , x′-is-close-to-x)


  {-
    Above, for a morphism f : A → B, we defined the induced
    dependent morphism  d f : (a : A) → formal-disk-at a → formal-disk-at (f a)
    if f is an equivalence, d f is an equivalence.
  -}


  module equivalences-induce-equivalences-on-formal-disks
    {A B : U₀} (f≃ : A ≃ B) where

    f = underlying-map-of f≃

    ℑf⁎-is-an-equivalence : (x y : A) → (λ (γ : x is-close-to y) → ℑ⁎ f ⁎ γ) is-an-equivalence
    ℑf⁎-is-an-equivalence =
      equivalences-induce-equivalences-on-the-coreduced-identity-types.ℑf⁎-is-an-equivalence f≃
    
    df-is-an-equivalence : (a : A) → (d f a) is-an-equivalence
    df-is-an-equivalence a =
      fiber-equivalences-along-an-equivalence-on-the-base.induced-map-is-an-equivalence
        (λ x → a is-close-to x) (λ y → f a is-close-to y) f≃
        (λ x →
           (λ (γ : a is-close-to x) → ℑ⁎ f ⁎ γ) is-an-equivalence-because
           ℑf⁎-is-an-equivalence a x)
           
    conclusion : (a : A) → formal-disk-at a ≃ formal-disk-at (f a)
    conclusion a = (d f a) is-an-equivalence-because (df-is-an-equivalence a)

