{-# OPTIONS --without-K --cubical #-}

module CDCHoTT.Experimental.CubicalZ where

  open import Cubical.Foundations.Everything renaming (_∘_ to _∘'_ ; id to idfunc)
  open import CDCHoTT.Basics
  
  data ℤ : U lzero where
    zero : ℤ
    pre : ℤ → ℤ
    suc : ℤ → ℤ
    linv : (x : ℤ) → pre (suc x) ≡ x
    rinv : (x : ℤ) → suc (pre x) ≡ x
  
  experiment1 : pre ∘ suc ≡ λ a → a
  experiment1 i x = linv x i

  lemma1 : (x : ℤ) → suc (pre (pre x)) ≡ pre x
  lemma1 x i = rinv (pre x) i

  lemma2 : (x y : ℤ) → x ≡ y → suc x ≡ suc y 
  lemma2 x y p = λ i → suc (p i)

  lemma3 : (x y : ℤ) → x ≡ y → pre x ≡ pre y 
  lemma3 x y p = λ i → pre (p i)

 {- lemma2' : (x y : ℤ) → suc x ≡ suc y → pre (suc x) ≡ pre (suc y) 
  lemma2' x y p =  lemma3 (suc x) (suc y) p

  lemma2'' :  (x y : ℤ) → pre (suc x) ≡ pre (suc y) → x ≡ y
  lemma2'' x y p = λ i → (linv x ⁻¹ ∙ p ∙ linv y) i

  lemma2''' :  (x y : ℤ) → suc x ≡ suc y → x ≡ y
  lemma2''' x y p = lemma2'' x y (lemma2' x y p)

  lemma3' : (x y : ℤ) → pre x ≡ pre y → suc (pre x) ≡ suc (pre y) 
  lemma3' x y p =  lemma2 (pre x) (pre y) p

  lemma3'' :  (x y : ℤ) → suc (pre x) ≡ suc (pre y) → x ≡ y
  lemma3'' x y p = λ i → (rinv x ⁻¹ ∙ p ∙ rinv y) i

  lemma3''' :  (x y : ℤ) → pre x ≡ pre y → x ≡ y
  lemma3''' x y p = lemma3'' x y (lemma3' x y p)
-}

  experiment2 : (x : ℤ) → suc (suc (pre (pre x))) ≡ x
  experiment2 x = lemma2 (suc (pre (pre x)))
                         (pre x)
                         (λ i → rinv (lemma3 x x refl i) i)
                   ∙ rinv x


  _+_ : ℤ → ℤ → ℤ
  zero + x = x
  pre x + y = pre (x + y)
  suc x + y = suc (x + y)
  linv x i + y = linv (x + y) i
  rinv x i + y = rinv (x + y) i

  _+'_ : ℤ → ℤ → ℤ
  x +' zero = x
  x +' pre y = pre (x +' y) 
  x +' suc y = suc (x +' y)
  x +' linv y i = linv (x +' y) i
  x +' rinv y i = rinv (x +' y) i

  data 𝕊 : U lzero where
    base : 𝕊
    loop : base ≡ base

  -- ℤ' is a group with operation = composition, neutral = refl, and associativity = associativity of paths...
  -- That is,  ℤ' is the group of integers, while ℤ is the inductive type of integers
   
  ℤ' = base ≡ base
  [0] = refl
  [1] = loop
  [-1] = loop ⁻¹
  [2] = loop ∙ loop
  [-2] = (loop ∙ loop) ⁻¹
  -- etc...

  pathComp-r-fixed :  ∀ {i} {A : U i} {x y z : A} (p : x ≡ y) (q : y ≡ z)(r : x ≡ y) → (p ≡ r) → p ∙ q ≡ r ∙ q
  pathComp-r-fixed {x = x} p q r s = λ i j → hcomp (doubleComp-faces (λ _ → x) q j) (s i j) 
  pathComp-l-fixed :  ∀ {i} {A : U i} {x y z : A} (p : x ≡ y) (q : z ≡ x)(r : x ≡ y) → (p ≡ r) → q ∙ p ≡ q ∙ r
  pathComp-l-fixed {z = z} p q r s = λ i j → hcomp (doubleComp-faces (λ _ → z) (s i) j) (q j)   


  linv' : (p : ℤ') →  p ∙ loop ∙ loop ⁻¹  ≡ p
  linv' p = pathComp-l-fixed (loop ∙ loop ⁻¹) p refl (rCancel loop) ∙ rUnit p ⁻¹
  --rinv' : (x : ℤ') → suc (pre x) ≡ x

  
  data _≣₀_≣₀_ {i} {A : U i} (a b : A) : A → U i where  
    refl₀₁ : a ≣₀ b ≣₀ a
    refl₀₂ : a ≣₀ b ≣₀ b

  _o_ : {i : Level} {A : U i} {a b c d : A} →  a ≣₀ b ≣₀ c → b ≣₀ c ≣₀ d →  a ≣₀ b ≣₀ d   
  refl₀₁ o refl₀₁ = refl₀₂
  refl₀₂ o refl₀₁ = refl₀₂
  refl₀₁ o refl₀₂ = refl₀₁
  refl₀₂ o refl₀₂ = refl₀₂

  op : {i : Level} {A : U i} {a b c d : A} →  a ≣₀ c ≣₀ b → c ≣₀ b ≣₀ a →  a ≣₀ c ≣₀ a   
  op = λ x y → x o y

  L[_]⁻¹ :  {i : Level} {A : U i} {a b c : A} →  a ≣₀ b ≣₀ c →  b ≣₀ a ≣₀ c
  L[ refl₀₁ ]⁻¹ = refl₀₂
  L[ refl₀₂ ]⁻¹ = refl₀₁

  data _≣₀_≣₁_ {i} {A : U i} (a b : A) : A → U i where  
     reflₐ : a ≣₀ b ≣₁ a 

  _o'_ : {i : Level} {A : U i} {a b c d : A} →  a ≣₀ b ≣₁ c → b ≣₀ c ≣₁ d →  a ≣₀ b ≣₁ d   
  reflₐ o' reflₐ = {!!}

  


  
