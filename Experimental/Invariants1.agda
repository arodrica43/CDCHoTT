{-# OPTIONS --no-positivity-check --cubical #-}

module CDCHoTT.Experimental.Invariants1 where

  open import Cubical.Foundations.Everything renaming (id to identity)
  
  data ⊥ : Set where

  recipr : {X Y : Set} → (X → Y) → ((Y → ⊥) → (X → ⊥))
  recipr f = λ g x → g (f x)

  data Bad : Set where
     bad : (Bad → ⊥) → Bad

  self-app : Bad → ⊥
  self-app (bad f) = f (bad f)

  absurd : ⊥
  absurd = self-app (bad self-app)

  data 𝟙 {l : Level} : Type l  where
    ∗₁ : 𝟙

  data 𝕊 {l : Level} : Type l  where
    ∗ₛ : 𝕊
    ↺ : ∗ₛ ≡ ∗ₛ


  PointedType : {l : Level} → Type (ℓ-suc l) -- Create a "category" of pointed objects in every type level.
  PointedType {l = l} = Σ (Type l)  λ X → X

  id-of-pt-as-pt : {l : Level} → ((X,p) : PointedType) → (x : fst (X,p)) → PointedType {l}
  id-of-pt-as-pt (X,p) x = (x ≡ x) , refl
    
  𝕊-as-pt : {l : Level} → PointedType {l}
  𝕊-as-pt = 𝕊 , ∗ₛ

  idₛ-as-pt : {l : Level} → PointedType {l}
  idₛ-as-pt = id-of-pt-as-pt 𝕊-as-pt ∗ₛ

  DiscrDynSys : {l : Level} → Type (ℓ-suc l)
  DiscrDynSys {l = l} = Σ (Type l) λ X → X → X

  Mon : {l : Level} → Type (ℓ-suc l) 
  Mon {l = l} =  Σ (Type l) λ X → X → X → X

  Hom : {l : Level}{P : Type l → Type l} → (X Y : Σ (Type l) P) → (cond : (fst X → fst Y) → Type l ) → Type l
  Hom X Y cond = Σ (fst X → fst Y) cond

  --example of hom types of pointed spaces:

  Hom[PointedType] : {l : Level} → ((X,p) (Y,q) : PointedType {l}) → Type l
  Hom[PointedType] A B = Hom A B λ f → f (snd A) ≡ snd B

  --example of hom types of discrete dynamical systems with conjugation of systems as morphisms:

  Hom[DiscrDynSys] : {l : Level} → ((X,p) (Y,q) : DiscrDynSys {l}) → Type l
  Hom[DiscrDynSys] A B = Hom A B λ f → (snd B) ∘ f ≡ f ∘ (snd A)

  --example of hom types of monoids:

  linearity1 : {l : Level} → (M N : Mon {l}) → (f : fst M → fst N) → Type l
  linearity1 M N f = (x y : fst M) → f ((snd M) x y) ≡ (snd N) (f x) (f y) -- f (x + y) = f(x) + f(y)
  
  Hom[Mon] : {l : Level} → ((X,p) (Y,q) : Mon {l}) → Type l
  Hom[Mon] A B = Hom A B λ f → linearity1 A B f

  --Orbits of of a discrete dynamical system

  data ℕ {l : Level} : Type l where
    zero : ℕ
    succ : ℕ {l} → ℕ

  id : {l : Level}{X : Type l} → (X → X)
  id {X = X} = λ X → X
  
  apply : {l : Level}{X : Type l} → (f : X → X) → (n : ℕ {l}) → (X → X)
  apply f zero = id
  apply f (succ n) = f ∘ (apply f n)
  
  𝓞 : {l : Level}{S : DiscrDynSys {l}} → (x : fst S) → Type l
  𝓞 {S = S} x = Σ (fst S) λ y →
                  Σ ℕ λ n →
                    (apply (snd S) n) x ≡ y

