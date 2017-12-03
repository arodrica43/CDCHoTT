{-# OPTIONS --without-K #-}


{-

  This module is about the homogeneous structure on ℑ(A), 
  where A is a homogeneous type.
  It turns out to be a homogeneous type again 
   -- as well as its 'kernel' 𝔻ₑ

  The arguments are basically the same as those in 'Im.agda' 
  in the section on left invertible structures on ℑ(A),
  for some left invertible A. The homogeneous types are 
  a replacement for the left invertible H-spaces.

  The name of this module is a pathetic pun.

-}

module ImHomogeneousType where
  open import Basics 
  open import EqualityAndPaths renaming (_⁻¹ to _⁻¹•)
  open import Homotopies
  open import Language
  open import Equivalences
  open import CommonEquivalences
  open import HomogeneousType
  open import Im
  open import FormalDisk

  module homogene-ℑ-sequence {A : 𝒰} (A′ : homogeneous-structure-on A) where
    open homogeneous-structure-on_ A′

    ιe = ι e

    ℑψ : (x : ℑ A) → ℑ A ≃ ℑ A
    ℑψ = ℑ-induction
             (λ _ → ℑ≃-is-coreduced)
             λ (x : A) → ℑ≃ (ψ x)

    compute-ℑψ :
      ∀ (x : A)
      → ℑψ (ι x) ≈ ℑ≃ (ψ x)
    compute-ℑψ = ℑ-compute-induction (λ _ → ℑ≃-is-coreduced) λ (x : A) → ℑ≃ (ψ x)
    
    ℑψ-is-a-family-of-translations :
      (x : ℑ A) → (ℑψ x $≃ ιe) ≈ x
    ℑψ-is-a-family-of-translations =
      ℑ-induction
        (λ _ → coreduced-types-have-coreduced-identity-types _ (ℑ-is-coreduced _) _ _)
        λ a → ℑψ (ι a) $≃ ιe
             ≈⟨ (λ χ → χ $≃ ιe) ⁎  ℑ-compute-induction (λ _ → ℑ≃-is-coreduced) (λ (x : A) → ℑ≃ (ψ x)) a ⟩
              ℑ≃ (ψ a) $≃ ιe
             ≈⟨ naturality-of-ℑ-unit≃ (ψ a) e ⟩
              ι (ψ a $≃ e)
             ≈⟨ ℑ-unit ⁎ is-translation-to a ⟩
               ι a
             ≈∎

    structure : homogeneous-structure-on (ℑ A)
    structure = record { e = ιe ; ψ = ℑψ ; is-translation-to = ℑψ-is-a-family-of-translations }

    
    ψ′ : (x : A)
       → A → A
    ψ′ x = underlying-map-of (ψ x)
        
    ℑψ′ : (x : ℑ A)
        → ℑ A → ℑ A
    ℑψ′ x = underlying-map-of (ℑψ x)

    ι-commutator :
      ∀ (x y : A)
      → ℑψ (ι x) $≃ (ι y)  ≈  ι (ψ x $≃ y)
    ι-commutator x y =
      let
        compute-ℑψ′ : 
          ∀ (x : A)
          → ℑψ′ (ι x) ≈ ℑ→ (ψ′ x)
        compute-ℑψ′ x = underlying-map-of ⁎ (compute-ℑψ x)
        
      in ℑψ′ (ι x) (ι y)
        ≈⟨ (λ f → f (ι y)) ⁎ compute-ℑψ′ x ⟩
         ℑ→ (ψ′ x) (ι y)
        ≈⟨ naturality-of-ℑ-unit (ψ′ x) y ⟩
         ι (ψ′ x y)
        ≈∎ 


    𝔻ₑ′ : A → 𝒰
    𝔻ₑ′ a = e is-infinitesimally-close-to a

    𝔻ₑ = 𝔻 _ e

    e-𝔻ₑ : 𝔻ₑ
    e-𝔻ₑ = ∗-𝔻
  
    ψ-𝔻ₑ′ :
         ∀ (d : 𝔻ₑ) (a : A)
         → 𝔻ₑ′ a ≃ 𝔻ₑ′ (ψ′ (∑π₁ d) a)
         
    ψ-𝔻ₑ′ (x , γ) a =
         𝔻ₑ′ a
        ≃⟨ equivalent-by-definition ⟩
          e is-close-to a
        ≃⟨ equivalent-by-definition ⟩
          (ι e)  ≈  (ι a)
        ≃⟨ ℑψ (ι x) ∗≃ ⟩ 
          ℑψ′ (ι x) (ι e)  ≈  ℑψ′ (ι x) (ι a) 
        ≃⟨  ℑψ-is-a-family-of-translations (ι x) ⁻¹• •l≃  ⟩ 
          ι x  ≈  ℑψ′ (ι x) (ι a) 
        ≃⟨  γ •l≃  ⟩ 
          ι e  ≈  ℑψ′ (ι x) (ι a)
        ≃⟨ (ι-commutator x a •r≃) ⟩
          ι e  ≈ ι (ψ′ x a) 
        ≃⟨ equivalent-by-definition ⟩
          𝔻ₑ′ (ψ′ x a)
        ≃∎

    import DependentTypes
    open DependentTypes.fiber-equivalences-along-an-equivalence-on-the-base 𝔻ₑ′ 𝔻ₑ′

    ψ-𝔻ₑ : ∀ (d : 𝔻ₑ) → 𝔻ₑ ≃ 𝔻ₑ
    ψ-𝔻ₑ (x , γ) =
      induced-map (ψ x) (ψ-𝔻ₑ′ (x , γ)) 
      is-an-equivalence-because
      induced-map-is-an-equivalence (ψ x) (ψ-𝔻ₑ′ (x , γ)) 

    ψ-𝔻ₑ″ : ∀ (d : 𝔻ₑ) → 𝔻ₑ → 𝔻ₑ
    ψ-𝔻ₑ″ d = underlying-map-of (ψ-𝔻ₑ d)
{-
    ψ-𝔻ₑ-translates :
      ∀ (d : 𝔻ₑ)
      →  (ψ-𝔻ₑ d) $≃ e-𝔻ₑ  ≈  d
    ψ-𝔻ₑ-translates (x , γ) = {!!}

    homogeneous-structure : homogeneous-structure-on 𝔻ₑ
    homogeneous-structure =
      record { e = e-𝔻ₑ ;
               ψ = ψ-𝔻ₑ ;
               is-translation-to = ψ-𝔻ₑ-translates } 
-}
{- 
    𝒯 :
      ∀ (x : A)
      → K′ (ψ A′ x $≃ e A′) ≃ K′ x
    𝒯 x = transport-as-equivalence K′ (is-translation-to A′ x)
    -- K′ e   ≃   φ e ≈ e B′  ≃   K′ x
    the-ψ-K′-translate :
      ∀ (p : K)
      → (𝒯 (∑π₁ p) ∘≃ ψ-K′ p (e A′)) $≃ φ-respects-e  ≈  ∑π₂ p
    the-ψ-K′-translate (x , γ) =
       (𝒯 x ∘≃ ψ-K′ (x , γ) (e A′)) $≃ φ-respects-e
      ≈⟨ {!!} ⟩
       γ
      ≈∎

-}
