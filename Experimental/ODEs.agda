{-# OPTIONS --without-K #-}

module CDCHoTT.Experimental.ODEs where

  open import CDCHoTT.Basics
  open import CDCHoTT.EqualityAndPaths
  open import CDCHoTT.FormalDiskBundle

 

  postulate
    i j : Level
    X Y : U i

  Aut : {k : Level} →  U k → U k
  Aut X = X → X

  Hom : {k : Level} → U k → U k → U k
  Hom X Y = X → Y 

  f : Hom (X × Y) (Y × X)
  f z = (π₂ z , π₁ z)

  preimage : {k : Level}{A B : U k} → Hom A B → B → U k -- preimage up to homotopy = preimage of connected components 
  preimage {A = A} f y = Σ A λ x → f x ≈ y

  [_]⁻¹ : {k : Level}{A B : U k} → Hom A B → B → U k
  [ f ]⁻¹ =  preimage f

  ι :  {k : Level}{A B : U k} {f : Hom A B}{y : B} → [ f ]⁻¹ y → A
  ι z = Σπ₁ z

  Lemma1 :  {k : Level}{A B : U k} {f : Hom A B}{x : A} → (z : [ f ]⁻¹ (f x)) → [ f ]⁻¹ (f (ι z)) ≈ [ f ]⁻¹ (f x)  
  Lemma1 {f = f} z = transport (λ x →  [ f ]⁻¹ (f (ι z)) ≈ [ f ]⁻¹ x  ) (Σπ₂ z) refl

  Lemma2 :  {k : Level}{A B : U k} {f : Hom A B}{x : A} → (z : [ f ]⁻¹ (f x)) →  (f (ι z)) ≈ f x
  Lemma2 z = Σπ₂ z

  data LT (k : Level) : U k where
    ∞ : LT k
    ⟶ : LT lzero → LT k

  Bund : {k : Level} → (X : U k) → U (lsuc k)
  Bund {k = k} X = Σ (U k) λ Y → (Y → X)

  Bund⊂U : {k : Level} {X : U k} → (f : Bund X) → U k
  Bund⊂U f = Σπ₁ f

  Sect : {k : Level} {X : U k} → (f : Bund X) → U k
  Sect {X = X} f = Σ (X → Bund⊂U f) λ s → (s ∘ (Σπ₂ f) ≈ id)

  Retr : {k : Level} {X : U k} → (f : Bund X) → U k
  Retr {X = X} f = Σ (X → Bund⊂U f) λ s → ((Σπ₂ f) ∘ s ≈ id)

  Iso : {k : Level} (X Y : U k) → U k
  Iso X Y = Σ (X → Y) λ f → (Σ (Y → X) λ g → (f ∘ g ≈ id) × ( g ∘ f ≈ id))

  Iso→Bund : {k : Level} {X Y : U k} → (f : Iso Y X) → Bund X
  Iso→Bund {X = X} {Y = Y} f = Y , Σπ₁ f

  Iso→Sect : {k : Level} {X Y : U k} → (f : Iso Y X) → Sect (Iso→Bund f)
  Iso→Sect f = Σπ₁ (Σπ₂ f) , π₂ (Σπ₂ (Σπ₂ f))

  Iso→Retr : {k : Level} {X Y : U k} → (f : Iso Y X) → Retr (Iso→Bund f)
  Iso→Retr f = Σπ₁ (Σπ₂ f) , π₁ (Σπ₂ (Σπ₂ f))





