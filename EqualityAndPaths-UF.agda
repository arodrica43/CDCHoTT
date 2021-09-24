{-# OPTIONS --without-K --cubical #-}

module CDCHoTT.EqualityAndPaths-UF where
  open import CDCHoTT.Basics
  open import Cubical.Foundations.Id
  --open import Cubical.Foundations.Everything
  --open import Cubical.Core.HoTT-UF
  --open import Cubical.Core.Everything
  
  {-
  infix 5 _≈_                                         -- \approx
  data _≈_ {i} {A : U i} (a : A) : A → U i where  
    id : a ≈ a

   
  -- concatenation of paths
  infixl 50 _•_ -- \bu
  _•_ : ∀ {i} {A : U i} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  refl • γ = γ
  -}
  

  𝟙-contraction : (x : 𝟙) → x ≡ ∗
  𝟙-contraction ∗ = refl

  refl-self-id-r : ∀ {i} {a : U i} {x y : a} → (refl {x = y} ≡ (refl ∙ refl))
  refl-self-id-r = refl

  refl-self-id-l : ∀ {i} {a : U i} {x y : a} → (refl {x = x} ≡ (refl ∙ refl))
  refl-self-id-l = refl
  
  refl-is-r-neutral : ∀ {i} {a : U i} {x y : a} (γ : x ≡ y) → (γ ≡ (γ ∙ refl)) 
  refl-is-r-neutral {x = x} {y = y} p =  J (λ y₁ x₁ → x₁ ≡ (x₁ ∙ refl)) (refl-self-id-r {x = x}) p {- This case can be solved by refl directly -}
  refl-is-l-neutral : ∀ {i} {a : U i} {x y : a} (γ : x ≡ y) → (γ ≡ (refl ∙ γ)) 
  refl-is-l-neutral {i} {a = a} {x = x} {y = y} p = J (λ y₁ x₁ → x₁ ≡ (refl ∙ x₁)) (refl-self-id-r {x = x}) p
  
  ptransp : ∀ {i j} {A : U i}  {x y : A} → (P : A → U j) → (γ : x ≡ y) → (P x → P y)
  ptransp P p z = transport P p z {- The same transport as in HoTT -}

  apply_to-path : {A B : 𝒰₀} {x y : A} (f : A → B) → x ≡ y → f(x) ≡ f(y)
  apply f to-path p = ap f p {- k  could be substituted by i (?) -}

  apd : ∀ {i j} {A : U j} {x y : A} → (P : A → U i) → (s : (a : A) → P a) → (γ : x ≡ y) → (ptransp P γ (s x) ≡  s y)
  apd {A = A} {x = x} {y = y} P s p = {!!} {- inspired by transport-filler from Prelude -}

{-    
  •-is-associative : ∀ {i} {A : U i} {w x y z : A} (γ : w ≡ x) (γ′ : x ≡ y) (γ″ : y ≡ z) → γ ∙ (γ′ ∙ γ″) ≡ (γ ∙ γ′) ∙ γ″
  •-is-associative p q r = assoc p q r
  
  ∘-is-associative : ∀ {i} {A B C D : U i} → (f : A → B) → (g : B → C) → (h : C → D) → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
  ∘-is-associative f g h = refl

   
  ⁻¹-is-right-inversion : ∀ {i} {A : U i} {x y : A}  (γ : x ≡ y) → γ ∙ γ ⁻¹ ≡ refl
  ⁻¹-is-right-inversion p = rCancel p
   
  ⁻¹-is-left-inversion : ∀ {i} {A : U i} {x y : A}  (γ : x ≡ y) → γ ⁻¹ ∙ γ ≡ refl
  ⁻¹-is-left-inversion p = lCancel p


 {- ⁻¹-product-filler : ∀ {ℓ} {A : Type ℓ} {x y z : A} (p : x ≡ y)(q : y ≡ z) → (j i : I) → A
  ⁻¹-product-filler {x = x} {y} {z = z} p q j i =
    hfill (λ k → λ { (i = i0) → x
                   ; (i = i1) → z
                   ; (j = i0) →  hcomp (doubleComp-faces (λ _ → x) q i) (p i)
                   ; (j = i1) →  hcomp (doubleComp-faces (λ _ → z) (p ⁻¹) (~ i)) ((q ⁻¹) (~ i))}) (inS ((p ∙ q) {!!})) j

-}

  
  apply_to-path : {A B : 𝒰₀} {x y : A} (f : A → B) → x ≡ y → f(x) ≡ f(y)
  apply f to-path p = λ i → funExt (λ j k → f (p k)) i p {- k  could be substituted by i (?) -}
  

  Hl :  ∀ {i} {A : U i} {x y z : A} (p : x ≡ y) (q : y ≡ z) → ((p ∙ q) ⁻¹) ∙ (p ∙ q) ≡ refl
  Hl p q = lCancel (p ∙ q)

  H1 :  ∀ {i} {A : U i} {x y z : A} (p : x ≡ y) (q : y ≡ z) → ((p ∙ q) ⁻¹) ∙ (p ∙ q) ≡ refl
  H1 p q = lCancel (p ∙ q)

  H13 :  ∀ {i} {A : U i} {x y z : A} (p : x ≡ x) (q : x ≡ y) → (p ≡ refl) → q ≡ p ∙ q
  H13 p q a = λ i j → refl-is-l-neutral (transport ({!!}) a) i j
{-
  H12 :  ∀ {i} {A : U i} {x y z : A} (p : x ≡ x) (q : x ≡ y) → (p ≡ refl) → p ∙ q ≡ refl ∙ q
  H12 {A = A} {x = x} {y = y} p q a = λ i j → compPath-filler (p ∙ q) (q ⁻¹) {!i!} i

  H2 :  ∀ {i} {A : U i} {x y z : A}  (p : x ≡ y) (q : y ≡ z) → ((p ∙ q) ⁻¹) ∙ (p ∙ q) ≡ refl → (((p ∙ q) ⁻¹) ∙ (p ∙ q)) ∙ (q ⁻¹) ≡ refl ∙ (q ⁻¹)
  H2 p q h1 = H12 ((((p ∙ q) ⁻¹) ∙ (p ∙ q))) (q ⁻¹) h1
-}
{-  ⁻¹-of-product : ∀ {i} {A : U i} {x y z : A}  (p : x ≡ y) (q : y ≡ z) →  (p ∙ q) ⁻¹ ≡ (q ⁻¹ ∙ p ⁻¹)
  ⁻¹-of-product {x = x} {y = y} {z = z} p q i j =   {!!} {- ⁻¹-product-filler p q i j -} -}
  ⁻¹-is-selfinverse : ∀ {i} {A : U i} {x y : A}  (γ : x ≡ y) → (γ ⁻¹) ⁻¹ ≡ γ
  ⁻¹-is-selfinverse p = refl

  invert-both-sides : ∀ {A : 𝒰₀} {a a′ : A} {γ γ′ : a ≡ a′}
                    → γ ≡ γ′ → γ ⁻¹ ≡ γ′ ⁻¹
  invert-both-sides H = λ i j → H i (~ j)

 -- apply_to-path : {A B : 𝒰₀} {x y : A} (f : A → B) → x ≡ y → f(x) ≡ f(y)
 -- apply f to-path p = λ i → funExt (λ j k → f (p k)) i p {- k  could be substituted by i (?) -}
  
-}
{- 
                
  
  -- application extends to paths
  apply_to-path : {A B : 𝒰₀} {x y : A} (f : A → B) → x ≈ y → f(x) ≈ f(y)
  apply f to-path refl = refl
  
  
  infixr 70 _⁎_  -- \asterisk
  _⁎_ : ∀ {i j} {A : U i} {B : U j} {x y : A} (f : A → B) → x ≈ y → f(x) ≈ f(y)
  _⁎_ {_} {_} {_} {_} {x} {.x} f  refl = refl {a = f(x)} 

  ap : ∀ {i j} {A : U i} {B : U j} {x y : A} (f : A → B) → x ≈ y → f(x) ≈ f(y)
  ap f γ = f ⁎ γ

  apply-preserves-refl : {A B : 𝒰₀} {x : A} (f : A → B) → f ⁎ refl {a = x} ≈ refl {a = f(x)}
  apply-preserves-refl f = refl
  
  application-commutes-with-composition :
    ∀ {A B C : 𝒰₀} {a a′ : A}
      → (f : A → B) → (g : B → C)
      → (γ : a ≈ a′)
      → g ⁎ (f ⁎ γ) ≈ (g ∘ f) ⁎ γ
  application-commutes-with-composition f g refl = refl
  
  apply-commutes-with-evaluation : ∀ {A B C : 𝒰₀} {a a′ : A}
                                   → (γ : a ≈ a′) → (b : B)
                                   → (f : A → B → C)
                                   → (λ g → g b) ⁎ (f ⁎ γ) ≈ ((λ g → λ a → g a b) f) ⁎ γ
  apply-commutes-with-evaluation refl b f = refl
  
  application-commutes-with-inversion : ∀ {i j} {A : U i} {B : U j} {a a′ : A}
                                      → (f : A → B) → (γ : a ≈ a′)
                                      → f ⁎ (γ ⁻¹) ≈ (f ⁎ γ) ⁻¹ 
  application-commutes-with-inversion f refl = refl
  
  application-commutes-with-concatenation : ∀ {A B : 𝒰₀} {a a′ a″ : A} (f : A → B) (γ : a ≈ a′) (γ′ : a′ ≈ a″)
                                          → f ⁎ (γ • γ′) ≈ (f ⁎ γ) • (f ⁎ γ′)
  application-commutes-with-concatenation f refl refl = refl                                        
  
  
  id-has-trivial-application : ∀ {A : 𝒰₀} {a a′ : A} 
                             → (γ : a ≈ a′)
                             → id ⁎ γ ≈ γ
  id-has-trivial-application refl = refl
  
  codomaining-has-trivial-application : ∀ {A : 𝒰₀} {a a′ : A}
                                        → (γ γ′ : a ≈ a′) → (ζ : γ ≈ γ′) 
                                        → (λ (η : a ≈ a′) → a′) ⁎ ζ ≈ refl
  codomaining-has-trivial-application γ .γ refl = refl
  
  
  -- calculate with equalities
  construct-path-in-∑ : ∀ {A : 𝒰₀} {P : A → 𝒰₀} (a a′ : A) (p : P a) (p′ : P a′)
                        → (γ : a ≈ a′) (η : transport P γ p ≈ p′)
                        → (a , p) ≈ (a′ , p′)
  construct-path-in-∑ a .a _ _ refl η = (λ q → (a , q)) ⁎ η
  
  
  
  -- transport computations
  transport-is-contravariant :  ∀ {i j} {A : U i} {x y z : A} → (P : A → U j) → (γ : x ≈ y) → (γ′ : y ≈ z) 
                                → transport P γ′ ∘ transport P γ ≈ transport P (γ • γ′)
  transport-is-contravariant P refl relf = refl
  
  compute-endo-id-transport : ∀ {A : 𝒰₀} {a a′ : A} (f : A → A) 
                              → (γ : a ≈ a′) 
                              → (η : f a ≈ a)
                              → transport (λ a → f a ≈ a) γ η ≈ (f ⁎ γ) ⁻¹ • η • γ
  compute-endo-id-transport f refl η = refl-is-right-neutral η
  
  compute-endo-apply-transport : 
    ∀ {A B : 𝒰₀} {a a′ : A} (f : A → B) 
    → (z z′ : B → B)
    → (ζ : z ≈ z′)
    → (η : z (f a) ≈ z (f a′))
    → transport (λ (z : B → B) → z (f a) ≈ z (f a′)) ζ η  
      ≈ (λ (w : B → B) → w (f a)) ⁎ ζ ⁻¹ • η •
        (λ (w : B → B) → w (f a′)) ⁎ ζ
  compute-endo-apply-transport f z .z refl η = refl-is-right-neutral η
  
  
  _is-a-proposition : ∀ {i} (A : U i) → U i
  A is-a-proposition = (x y : A) → x ≈ y
  
  in-the-type_we-have-an-equality_≈_ : ∀ (A : 𝒰₀) → A → A → 𝒰₀
  in-the-type A we-have-an-equality x ≈ y = x ≈ y
  
  ×-uniqueness : ∀ {A B : 𝒰₀} → (x : A × B) → x ≈ (π₁ x , π₂ x)
  ×-uniqueness (a , b) = refl
  
  ×-create-equality : ∀ {A B : 𝒰₀} {a a′ : A} {b b′ : B}
                      → (γ : a ≈ a′) → (η : b ≈ b′)
                      → (a , b) ≈ (a′ , b′)
  ×-create-equality refl refl = refl

  _,≈_ : ∀ {A B : 𝒰₀} {a a′ : A} {b b′ : B}
                      → (γ : a ≈ a′) → (η : b ≈ b′)
                      → (a , b) ≈ (a′ , b′)
  γ ,≈ η = ×-create-equality γ η

  _×≈_ = _,≈_

  ×-uniqueness-of-equality : 
    ∀ {A B : 𝒰₀} → {x y : A × B} → (γ : x ≈ y)
    → γ ≈ ×-uniqueness x • (×-create-equality (π₁ ⁎ γ) (π₂ ⁎ γ)) • ×-uniqueness y ⁻¹
  ×-uniqueness-of-equality {_} {_} {x} {.x} refl = ⁻¹-is-right-inversion (×-uniqueness x) ⁻¹ •
                                            (λ η → η • ×-uniqueness x ⁻¹) ⁎
                                            refl-is-right-neutral (×-uniqueness x)
  ×-compute-π₁-of-equality : 
    ∀ {A B : 𝒰₀} {a a′ : A} {b b′ : B}
    → (γ : a ≈ a′) → (η : b ≈ b′)
    → π₁ ⁎ ×-create-equality γ η ≈ γ
  ×-compute-π₁-of-equality refl refl = refl
  
  ×-compute-π₂-of-equality : 
    ∀ {A B : 𝒰₀} {a a′ : A} {b b′ : B}
    → (γ : a ≈ a′) → (η : b ≈ b′)
    → π₂ ⁎ ×-create-equality γ η ≈ η
  ×-compute-π₂-of-equality refl refl = refl
  
  equality-action-on-∑ :
    ∀ {i} {j} {A : U i} {P : A → U j}
    → (a a′ : A) → (γ : a ≈ a′) → (pₐ : P a)
    → (a , pₐ) ≈ (a′ , transport P γ pₐ)
  equality-action-on-∑ a .a refl pₐ = refl
  
  cancel-equality-action-on-∑-with-projection :
    ∀ {i j} {A : U i} {P : A → U j}
    → (a a′ : A) → (γ : a ≈ a′) → (pₐ : P a)
    → ∑π₁ ⁎ (equality-action-on-∑ {_} {_} {A} {P} a a′ γ pₐ) ≈ γ
  cancel-equality-action-on-∑-with-projection a .a refl _ = refl
  
  inclusion-of-the-fiber-of_over_ :
    ∀ {i j} {A : U i} (P : A → U j)
    → (a : A) → (P a → ∑ P)
  inclusion-of-the-fiber-of_over_ P a pₐ = (a , pₐ)
  
  cancel-orthogonal-equality-in-∑ :
    ∀ {i j} {A : U i} {P : A → U j}
    → (a : A) (pₐ pₐ′ : P a) (γ : pₐ ≈ pₐ′)
    → ∑π₁ ⁎ (inclusion-of-the-fiber-of P over a) ⁎ γ ≈ refl 
  cancel-orthogonal-equality-in-∑ a pₐ .pₐ refl = refl
  
  --the-proposition-that-something-is-a-proposition-is-a-proposition : ∀ {i} (A : U i) → A is-a-proposition is-a-proposition
  --the-proposition-that-something-is-a-proposition-is-a-proposition {i} A p q = {!!}
  
  
  
  
  -- computations for transports
  compute-path-fibration-transport : 
    ∀ {A : 𝒰₀} (x₀ y z : A) (γ : y ≈ z) (η : x₀ ≈ y)
    → transport (λ x → x₀ ≈ x) γ η ≈ η • γ 
  compute-path-fibration-transport x₀ y .y refl η = 
    refl-is-right-neutral η
  
  
  -- equational reasoning
  infix 15 _≈∎    -- \approx\qed
  infixr 10 _≈⟨_⟩_    -- \approx\< \>
  
  _≈∎ : ∀ {i} {A : U i} (a : A)
        → a ≈ a
  a ≈∎ = refl 
  
  _≈⟨_⟩_ : ∀ {i} {A : U i} (a : A) {a′ a″ : A}
           → a ≈ a′ → a′ ≈ a″ → a ≈ a″
  a ≈⟨ γ ⟩ η = γ • η
  
  
  -- inequality
  _≠_ : {A : 𝒰₀} (a a′ : A) → 𝒰₀  -- \neq
  a ≠ a′ = a ≈ a → Zero
  

  -- do some stupid calculations needed in Im.agda
  stupid-but-necessary-calculation-with-associativity : 
    ∀ {A : 𝒰₀} {x y z w : A}
    → (γ : x ≈ y) (η : x ≈ z) (ζ : y ≈ w)
    → η • (η ⁻¹ • γ • ζ) • ζ ⁻¹ ≈ γ
  stupid-but-necessary-calculation-with-associativity refl refl refl =
     refl • (refl ⁻¹ • refl • refl) • refl ⁻¹
    ≈⟨ refl ⟩
     refl
    ≈∎

  another-stupid-but-necessary-calculation-with-associativity : 
    ∀ {A : 𝒰₀} {x y z w : A}
    → (γ : x ≈ y) (η : z ≈ x) (ζ : w ≈ y)
    → η ⁻¹ • (η • γ • ζ ⁻¹) • ζ ≈ γ
  another-stupid-but-necessary-calculation-with-associativity refl refl refl =
     refl ⁻¹ • (refl • refl • refl ⁻¹) • refl 
    ≈⟨ refl ⟩
     refl
    ≈∎


  calculation-for-im :
    ∀ {A : 𝒰₀} {x y : A}
    → (f : A → A)
    → (γ : f(x) ≈ y) (η : f(x) ≈ x)
    → (f ⁎ (η ⁻¹ • γ) ⁻¹) • γ ≈ (f ⁎ γ) ⁻¹ • (f ⁎ η) • γ  
  calculation-for-im f refl η =
     f ⁎ (η ⁻¹ • refl) ⁻¹ • refl
    ≈⟨ refl-is-right-neutral (f ⁎ (η ⁻¹ • refl) ⁻¹) ⁻¹ ⟩
     f ⁎ (η ⁻¹ • refl) ⁻¹
    ≈⟨ (λ γ →  γ ⁻¹) ⁎ application-commutes-with-concatenation f (η ⁻¹) refl ⟩ 
     ((f ⁎ (η ⁻¹)) • refl) ⁻¹
    ≈⟨ (λ γ → γ ⁻¹) ⁎ refl-is-right-neutral (f ⁎ (η ⁻¹)) ⁻¹ ⟩ 
     (f ⁎ (η ⁻¹)) ⁻¹
    ≈⟨ (λ γ → γ ⁻¹) ⁎ application-commutes-with-inversion f η • ⁻¹-is-selfinverse (f ⁎ η) ⟩ 
     f ⁎ η 
    ≈⟨ refl-is-right-neutral (f ⁎ η) ⟩ 
     f ⁎ η • refl
    ≈∎


  J-right :
    ∀ {A : 𝒰₀} {a : A} (C : (x : A) → a ≈ x → 𝒰₀)
    → (r : C a refl) → ((y : A) (γ : a ≈ y) → C y γ)
  J-right C r y refl = r 
-}
