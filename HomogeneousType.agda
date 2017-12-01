{-# OPTIONS --without-K #-}

module HomogeneousType where 
  open import Basics 
  open import EqualityAndPaths renaming (_⁻¹ to _⁻¹•)
  open import Homotopies
  open import Language
  open import Equivalences
  open import CommonEquivalences
  open import LeftInvertibleHspace
  
  {- 
    All points of a homogeneous space
    are equal up to an equivalence of the space.
    A homogeneous space 'A' is pointed by 'a₀'
    and 'ψ x' is an equivalence of 'A' mapping 'a₀' to 'x'.
  -} 
  record homogeneous-structure-on_ (A : U₀) : U₀ where
    field
      e : A
      ψ : (x : A) → (A ≃ A)
      is-translation-to : (x : A) → ((ψ x) $≃ e) ≈ x


  left-invertible-H-spaces-are-homogeneous :
    ∀ {A : U₀}
    → left-invertible-structure-on A → homogeneous-structure-on A
  left-invertible-H-spaces-are-homogeneous
    (structure-given-by-e= e ,μ= μ ,neutral-by left-neutral and right-neutral ,left-invertible-by left-invertible)
    = record {
        e = e ;
        ψ = λ x → (λ z → μ (z , x)) is-an-equivalence-because left-invertible x ;
        is-translation-to = left-neutral }


  
  
  
  record _─hom→_ {A B : U₀} (A′ : homogeneous-structure-on A) (B′ : homogeneous-structure-on B) : 𝒰 where
    open homogeneous-structure-on_
    field
      φ : A → B
      φ-respects-e : φ(e A′) ≈ e B′
      φ-respects-translations : (x y : A) → ψ B′ (φ x) $≃ (φ y) ≈ φ (ψ A′ x $≃ y)
                                        -- tanking translations commutes with φ
      -- this notion of morphism is problematic, since
      -- it turned out below in the kernel construction,
      -- that the commuter should be refl on ψ (φ x) e ≈ φ (ψ x e)
      -- but enforcing this would introduce another cell, which might
      -- lead to other cells.
      -- so I stopped here and tried to do what I want to know directly
      -- for the one known example of a morphism, i.e. the unit ι of ℑ
  
  module kernel {A B : 𝒰}
    {A′ : homogeneous-structure-on A} {B′ : homogeneous-structure-on B}
    (φ′ : A′ ─hom→ B′) where

    open homogeneous-structure-on_
    open _─hom→_ φ′

    K′ : A → 𝒰
    K′ a = φ a ≈ e B′

    K : 𝒰
    K = ∑ λ a → φ a ≈ e B′

    e-K : K
    e-K = (e A′ , φ-respects-e)

    ψ-K′ : ∀ (p : K)
      → (a : A) → K′ a ≃ K′ (ψ A′ (∑π₁ p) $≃ a)
    ψ-K′ (x , γ) a =
      let
        ψ-φ⟨x⟩ = ψ B′ (φ x)
        ψ-φ⟨x⟩′ = underlying-map-of ψ-φ⟨x⟩
        
      in  K′ a
        ≃⟨ equivalent-by-definition ⟩
          φ a  ≈  e B′
        ≃⟨ ψ-φ⟨x⟩ ∗≃ ⟩ 
          ψ-φ⟨x⟩′ (φ a)  ≈  ψ-φ⟨x⟩′ (e B′)
        ≃⟨ is-translation-to B′ (φ x) •r≃ ⟩ 
          ψ-φ⟨x⟩′ (φ a)  ≈  φ(x)
        ≃⟨ γ •r≃ ⟩ 
          ψ-φ⟨x⟩′ (φ a)  ≈  e B′
        ≃⟨ (φ-respects-translations x a •l≃) ⁻¹≃ ⟩
          φ (ψ A′ x $≃ a)  ≈  e B′
        ≃⟨ equivalent-by-definition ⟩
          K′ (ψ A′ x $≃ a)
        ≃∎

    import DependentTypes
    open DependentTypes.fiber-equivalences-along-an-equivalence-on-the-base K′ K′

    ψ-K : ∀ (p : K) → K ≃ K
    ψ-K (x , γ) =
      induced-map (ψ A′ x) (ψ-K′ (x , γ))
      is-an-equivalence-because
      induced-map-is-an-equivalence (ψ A′ x) (ψ-K′ (x , γ))

{- discontinued - reasons are at the morphism definition
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

    homogeneous-structure : homogeneous-structure-on K
    homogeneous-structure =
      record { e = e-K ;
               ψ = ψ-K ;
               is-translation-to = {!!} } 
-}
