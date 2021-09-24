{-# OPTIONS --without-K --cubical #-}

module CDCHoTT.EqualityAndPaths where
  open import CDCHoTT.Basics
  --open import Cubical.Foundations.Id
  open import Cubical.Foundations.Everything
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

  refl-is-r-neutral : ∀ {i} {a : U i} {x y : a} (γ : x ≡ y) → (γ ≡ (γ ∙ refl)) 
  refl-is-r-neutral {x = x} {y = y} p =  λ i j → compPath-filler p refl i j {- rUnit -}
  refl-is-l-neutral : ∀ {i} {a : U i} {x y : a} (γ : x ≡ y) → (γ ≡ (refl ∙ γ)) 
  refl-is-l-neutral {x = x} {y = y} p = λ i j → lUnit-filler p i1 i j  {- lUnit -}
   
  ptransp : ∀ {i j} {A : U i}  {x y : A} → (P : A → U j) → (γ : x ≡ y) → (P x → P y)
  ptransp P p z = transp (λ i → P (p i)) i0 z

  apd : ∀ {i j} {A : U j} {x y : A} → (P : A → U i) → (s : (a : A) → P a) → (γ : x ≡ y) → (ptransp P γ (s x) ≡  s y)
  apd {x = x}{y = y} P s p = λ i → transp (λ j → P (p (i ∨ j))) i (s (p i)) {- inspired by transport-filler from Prelude -}
    
  •-is-associative : ∀ {i} {A : U i} {w x y z : A} (γ : w ≡ x) (γ′ : x ≡ y) (γ″ : y ≡ z) → γ ∙ (γ′ ∙ γ″) ≡ (γ ∙ γ′) ∙ γ″
  •-is-associative p q r = assoc p q r
  
  ∘-is-associative : ∀ {i} {A B C D : U i} → (f : A → B) → (g : B → C) → (h : C → D) → h ∘ (g ∘ f) ≡ (h ∘ g) ∘ f
  ∘-is-associative f g h = refl

   
  ⁻¹-is-right-inversion : ∀ {i} {A : U i} {x y : A}  (γ : x ≡ y) → γ ∙ γ ⁻¹ ≡ refl
  ⁻¹-is-right-inversion p = rCancel p
   
  ⁻¹-is-left-inversion : ∀ {i} {A : U i} {x y : A}  (γ : x ≡ y) → γ ⁻¹ ∙ γ ≡ refl
  ⁻¹-is-left-inversion p = lCancel p
  
-- Theorem : Inverse of composition is the fliped composition of inverses  (p ∙ q)⁻¹ ≡ q⁻¹ ∙ p⁻¹ 

-- Base definitions
  pathComp-l-cancel :  ∀ {i} {A : U i} {x y z : A} (p : x ≡ y) (q : y ≡ z) → ((p ∙ q) ⁻¹) ∙ (p ∙ q) ≡ refl
  pathComp-l-cancel p q = lCancel (p ∙ q)
  pathComp-r-fixed :  ∀ {i} {A : U i} {x y z : A} (p : x ≡ y) (q : y ≡ z)(r : x ≡ y) → (p ≡ r) → p ∙ q ≡ r ∙ q
  pathComp-r-fixed {x = x} p q r s = λ i j → hcomp (doubleComp-faces (λ _ → x) q j) (s i j) 
  pathComp-l-fixed :  ∀ {i} {A : U i} {x y z : A} (p : x ≡ y) (q : z ≡ x)(r : x ≡ y) → (p ≡ r) → q ∙ p ≡ q ∙ r
  pathComp-l-fixed {z = z} p q r s = λ i j → hcomp (doubleComp-faces (λ _ → z) (s i) j) (q j)   

-- Full theorem (p ∙ q)⁻¹ ≡ q⁻¹ ∙ p⁻¹ without lemmas: ⁻¹-of-product ≡ ⁻¹-of-comp

  ⁻¹-of-comp :  ∀ {i} {A : U i} {x y z : A}  (p : x ≡ y) (q : y ≡ z) → (p ∙ q) ⁻¹ ≡ q ⁻¹ ∙ p ⁻¹  
  ⁻¹-of-comp p q = refl-is-r-neutral ((p ∙ q) ⁻¹)
                   ∙ pathComp-l-fixed refl ((p ∙ q) ⁻¹) (p ∙ p ⁻¹) (⁻¹-is-right-inversion p ⁻¹)
                   ∙ assoc ((p ∙ q) ⁻¹) p (p ⁻¹)
                   ∙ pathComp-r-fixed ((p ∙ q) ⁻¹ ∙ p) (p ⁻¹) (q ⁻¹) (refl-is-r-neutral ((p ∙ q) ⁻¹ ∙ p)
                     ∙ assoc ((p ∙ q) ⁻¹) p refl ⁻¹
                     ∙ (pathComp-l-fixed ( p ∙ (q ∙ (q ⁻¹))) ((p ∙ q) ⁻¹) ( p ∙ refl) (pathComp-l-fixed ((q ∙ (q ⁻¹))) p refl (rCancel q)) ) ⁻¹
                     ∙ pathComp-l-fixed (p ∙ (q ∙ q ⁻¹)) ((p ∙ q) ⁻¹) ( (p ∙ q) ∙ (q ⁻¹)) (assoc p q (q ⁻¹))
                     ∙  assoc (((p ∙ q) ⁻¹)) (p ∙ q) (q ⁻¹)
                     ∙ (λ i j → hcomp (doubleComp-faces (λ _ → q i1) (q ⁻¹) j) (pathComp-l-cancel p q i j))
                   ∙ refl-is-l-neutral (q ⁻¹) ⁻¹)

----------------------------------------------------------------------------------------------------------------------------

  ⁻¹-is-involution : ∀ {i} {A : U i} {x y : A}  (γ : x ≡ y) → (γ ⁻¹) ⁻¹ ≡ γ {- ≡ ⁻¹-is-selfinverse -}
  ⁻¹-is-involution p = refl

  invert-both-sides : ∀ {A : 𝒰₀} {a a′ : A} {γ γ′ : a ≡ a′} → γ ≡ γ′ → γ ⁻¹ ≡ γ′ ⁻¹
  invert-both-sides H = λ i j → H i (~ j)

    
  apply_to-path : {A B : 𝒰₀} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
  apply f to-path p = λ i → funExt (λ j k → f (p k)) i p {- k  could be substituted by i (?) -}
  
  
  infixr 70 _⁎_  -- \asterisk
  _⁎_ : ∀ {i j} {A : U i} {B : U j} {x y : A} (f : A → B) → x ≡ y → f(x) ≡ f(y)
  _⁎_ f p = λ i → funExt (λ _ j  → f (p j)) i p

  ap' : ∀ {i j} {A : U i} {B : U j} {x y : A} (f : A → B) → x ≡ y → f(x) ≡ f(y)
  ap' f γ = f ⁎ γ

  apply-preserves-refl : {A B : 𝒰₀} {x : A} (f : A → B) → f ⁎ refl {x = x} ≡ refl {x = f(x)}
  apply-preserves-refl f = refl

  application-commutes-with-composition : ∀ {A B C : 𝒰₀} {a a′ : A} → (f : A → B) → (g : B → C) → (γ : a ≡ a′) → g ⁎ (f ⁎ γ) ≡ (g ∘ f) ⁎ γ
  application-commutes-with-composition f g p = refl

  
  apply-commutes-with-evaluation : ∀ {A B C : 𝒰₀} {a a′ : A}
                                   → (γ : a ≡ a′) → (b : B)
                                   → (f : A → B → C)
                                   → (λ g → g b) ⁎ (f ⁎ γ) ≡ (λ x → f x b) ⁎ γ
  apply-commutes-with-evaluation p b f = refl

  application-commutes-with-inversion : ∀ {i j} {A : U i} {B : U j} {a a′ : A}
                                      → (f : A → B) → (γ : a ≡ a′)
                                      → f ⁎ (γ ⁻¹) ≡ (f ⁎ γ) ⁻¹ 
  application-commutes-with-inversion f p = refl

{-  
  application-commutes-with-concatenation : ∀ {A B : 𝒰₀} {a a′ a″ : A} (f : A → B) (p : a ≡ a′) (q : a′ ≡ a″)
                                          → (f ⁎ p) ∙ (f ⁎ q) ≡  f ⁎ (p ∙ q)
  application-commutes-with-concatenation {a = a} {a″ = a″} f p q = {!!}
-}

{-
  application-commutes-with-concatenation : ∀ {A B : 𝒰₀} {a a′ a″ : A} (f : A → B) (γ : a ≈ a′) (γ′ : a′ ≈ a″)
                                          → f ⁎ (γ • γ′) ≈ (f ⁎ γ) • (f ⁎ γ′)
  application-commutes-with-concatenation f refl refl = refl                                        
-}

 
  id-has-trivial-application : ∀ {A : 𝒰₀} {a a′ : A} 
                             → (γ : a ≡ a′)
                             → (λ x → x) ⁎ γ ≡ γ
  id-has-trivial-application p = refl

  codomaining-has-trivial-application : ∀ {A : 𝒰₀} {a a′ : A}
                                        → (p q : a ≡ a′) → (ζ : p ≡ q) 
                                        → (λ (η : a ≡ a′) → a′) ⁎ ζ ≡ refl
  codomaining-has-trivial-application p q r = refl

  partial-l-path : ∀ {i j} {A : U i} {P : A → U j} {a b : A} (p : a ≡ b)(i : I) → (a ≡ p i)
  partial-l-path p = λ i j → p (j ∧ i)

  partial-r-path : ∀ {A : 𝒰₀} {P : A → U ℓ-zero} {a b : A} (p : a ≡ b)(i : I) → (p i ≡ b)
  partial-r-path p = λ i j → p (i ∨ j)
{-  
  construct-path-in-∑-lemma : ∀ {A : 𝒰₀} {P : A → U ℓ-zero} (a b : A) (x : P a) (y : P b)(p : a ≡ b)(s : (a : A) → P a) → ((i : I) → P (p i)) 
  construct-path-in-∑-lemma {A = A} a b x y p s = λ i → (λ (z : A) → λ {(z = a) → x ; (z = b) → y}) (p i)
-}
{-
  construct-path-in-∑ : ∀ {i j}{A : U i} {P : A → U j} (a b : A) (x : P a) (y : P b ) (p : a ≡ b) (η : ptransp P p x ≡ y) → (a , x) ≡ (b , y)
  construct-path-in-∑ {j = j} {P = P} a b x y p η = λ i → ((λ z → p i , {!!}) ⁎ η) i
-}
   
{-  
  
  -- calculate with equalities
  construct-path-in-∑ : ∀ {A : 𝒰₀} {P : A → 𝒰₀} (a a′ : A) (p : P a) (p′ : P a′)
                        → (γ : a ≈ a′) (η : transport P γ p ≈ p′)
                        → (a , p) ≈ (a′ , p′)
  construct-path-in-∑ a .a _ _ refl η = (λ q → (a , q)) ⁎ η
  
-}

{-

  transport-is-contravariant :  ∀ {i j} {A : U i} {x y z : A} → (P : A → U j) → (γ : x ≡ y) → (γ′ : y ≡ z) 
                                → ptransp P γ′ ∘ ptransp P γ ≡ ptransp P (γ ∙ γ′)
  transport-is-contravariant P p q = λ i₁ a → {!!}
  
-}

{-
  
  -- transport computations
  transport-is-contravariant :  ∀ {i j} {A : U i} {x y z : A} → (P : A → U j) → (γ : x ≈ y) → (γ′ : y ≈ z) 
                                → transport P γ′ ∘ transport P γ ≈ transport P (γ • γ′)
  transport-is-contravariant P refl relf = refl

-}

{-
  compute-endo-id-transport : ∀ {A : 𝒰₀} {a a′ : A} (f : A → A) 
                              → (γ : a ≡ a′) 
                              → (η : f a ≡ a)
                              → (ptransp (λ a → f a ≡ a) γ η ≡ ((f ⁎ γ) ⁻¹) ∙ η ∙ γ)
  compute-endo-id-transport f p η = λ i j → {!!}  --refl-is-r-neutral η {!!} {!!}
-}
{-

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
