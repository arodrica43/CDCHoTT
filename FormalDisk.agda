{-# OPTIONS --without-K #-}

module FormalDisk where 
  open import Basics
  open import EqualityAndPaths
  open import Homotopies
  open import Language
  open import Equivalences
  open import CommonEquivalences  
  open import Pullback
  open import PullbackSquare
  open import Im
  open import InfinityGroups
  open import MayerVietoris
  open import EtaleMaps hiding (underlying-map-of)
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
    ∀ {X Y : U₀}
    → (f : X → Y)
    → (x : X) → 𝔻 _ x → 𝔻 _ (f x)
  induced-map-on-formal-disks f x (x′ , x′-is-close-to-x) =
    (f x′ , mapping-with f preserves-infinitesimal-proximity x′-is-close-to-x)


  -- the generalized differential of a function

  d :
    ∀ {X Y : U₀}
    → (f : X → Y)
    → (x : X) → 𝔻 _ x → 𝔻 _ (f x)
  d f x (x′ , x′-is-close-to-x) = induced-map-on-formal-disks f x (x′ , x′-is-close-to-x)

