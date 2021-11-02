module CDCHoTT.Experimental.HigherIds where

  open import CDCHoTT.Basics

   
  data _≡_ {i} {A : U i} (a : A) : A → U i where  
    rfl : a ≡ a

  _∙₁_ : {i : Level} {A : U i} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  rfl ∙₁ p = p

  ₁_⁻¹ : {i : Level} {A : U i} {x y : A} → x ≡ y → y ≡ x
  ₁ rfl ⁻¹ = rfl

  data _≡_≡_ {i} {A : U i} (a b : A) : A → U i where  
    [0] : a ≡ b ≡ a
    [1] : a ≡ b ≡ b
  
  _∙₂_ : {i : Level} {A : U i} {x y z w : A} → x ≡ y ≡ z → y ≡ z ≡ w → x ≡ y ≡ w -- this composition looks like an exponentiantion operation
  [0] ∙₂ [0] = [1]
  [1] ∙₂ [0] = [1]
  [0] ∙₂ [1] = [0]
  [1] ∙₂ [1] = [1]

  ₂_⁻¹ : {i : Level} {A : U i} {x y z : A} → x ≡ y ≡ z → y ≡ x ≡ z
  ₂ [0] ⁻¹ = [1]
  ₂ [1] ⁻¹ = [0]

  lemma1 : {i : Level} {A : U i} → (x y z : A) → x ≡ y ≡ z → x ≡ y → x ≡ z
  lemma1 x y z [0] rfl = rfl
  lemma1 x y z [1] rfl = rfl
 
  lemma2 : {i : Level} {A : U i} → (x y z : A) → x ≡ y ≡ z → x ≡ y → y ≡ z
  lemma2 x y z [0] rfl = rfl
  lemma2 x y z [1] rfl = rfl

  lemma3 : {i : Level} {A : U i} {x y z : A} → (s : x ≡ y ≡ z) → (p : x ≡ y) → (p ∙₁ lemma2 x y z s p) ≡ lemma1 x y z s p
  lemma3 [0] rfl = rfl
  lemma3 [1] rfl = rfl

  lemma1-1-a : {i : Level} {A : U i} {x y : A} → x ≡ y → x ≡ x ≡ x
  lemma1-1-a rfl = [0]
  lemma1-1-b : {i : Level} {A : U i} {x y : A} → x ≡ y → x ≡ x ≡ x
  lemma1-1-b rfl = [1]
  lemma1-2-a : {i : Level} {A : U i} {x y : A} → x ≡ y → y ≡ x ≡ x
  lemma1-2-a rfl = [0]
  lemma1-2-b : {i : Level} {A : U i} {x y : A} → x ≡ y → y ≡ x ≡ x
  lemma1-2-b rfl = [1]
  lemma1-3-a : {i : Level} {A : U i} {x y : A} → x ≡ y → x ≡ y ≡ x
  lemma1-3-a rfl = [0]
  lemma1-3-b : {i : Level} {A : U i} {x y : A} → x ≡ y → x ≡ y ≡ x
  lemma1-3-b rfl = [1]
  lemma1-4-a : {i : Level} {A : U i} {x y : A} → x ≡ y → x ≡ x ≡ y
  lemma1-4-a rfl = [0]
  lemma1-4-b : {i : Level} {A : U i} {x y : A} → x ≡ y → x ≡ x ≡ y
  lemma1-4-b rfl = [1]
  lemma1-5-a : {i : Level} {A : U i} {x y : A} → x ≡ y → y ≡ y ≡ x
  lemma1-5-a rfl = [0]
  lemma1-5-b : {i : Level} {A : U i} {x y : A} → x ≡ y → y ≡ y ≡ x
  lemma1-5-b rfl = [1]
  lemma1-6-a : {i : Level} {A : U i} {x y : A} → x ≡ y → x ≡ y ≡ y
  lemma1-6-a rfl = [0]
  lemma1-6-b : {i : Level} {A : U i} {x y : A} → x ≡ y → x ≡ y ≡ y
  lemma1-6-b rfl = [1]
  lemma1-7-a : {i : Level} {A : U i} {x y : A} → x ≡ y → y ≡ x ≡ y
  lemma1-7-a rfl = [0]
  lemma1-7-b : {i : Level} {A : U i} {x y : A} → x ≡ y → y ≡ x ≡ y
  lemma1-7-b rfl = [1]
  lemma1-8-a : {i : Level} {A : U i} {x y : A} → x ≡ y → y ≡ y ≡ y
  lemma1-8-a rfl = [0]
  lemma1-8-b : {i : Level} {A : U i} {x y : A} → x ≡ y → y ≡ y ≡ y
  lemma1-8-b rfl = [1]

  --lemma2-1-a : {i : Level} {A : U i} {x y z : A} → x ≡ y → x ≡ y ≡ z
  --lemma2-1-a rfl = lemma1-4-a {!!} -- needs a path x ~ z or y ∼ z
  lemma2-1-b : {i : Level} {A : U i} {x y z : A} → x ≡ y → x ≡ z ≡ y
  lemma2-1-b rfl = [0]
  --lemma2-2-a : {i : Level} {A : U i} {x y z : A} → x ≡ y → y ≡ x ≡ z
  --lemma2-2-a rfl = lemma1-4-a {!!} -- idem
  lemma2-2-b : {i : Level} {A : U i} {x y z : A} → x ≡ y → y ≡ z ≡ x
  lemma2-2-b rfl = [0]
  lemma2-3-a : {i : Level} {A : U i} {x y z : A} → x ≡ y → z ≡ x ≡ y
  lemma2-3-a rfl = [1]
  lemma2-3-b : {i : Level} {A : U i} {x y z : A} → x ≡ y → z ≡ y ≡ x
  lemma2-3-b rfl = [1]

  lemma3-1 : {i : Level} {A : U i} {x y z : A} → x ≡ y ≡ z → x ≡ y ≡ z
  lemma3-1 x = x  
  --lemma3-2 : {i : Level} {A : U i} {x y z : A} → x ≡ y ≡ z → x ≡ z ≡ y
  --lemma3-2 [0] = {![1]!} -- blocked
  --lemma3-2 [1] = [1] 
  lemma3-3 : {i : Level} {A : U i} {x y z : A} → x ≡ y ≡ z → y ≡ x ≡ z
  lemma3-3 [0] = [1]
  lemma3-3 [1] = [0]
  --lemma3-4 : {i : Level} {A : U i} {x y z : A} → x ≡ y ≡ z → y ≡ z ≡ x
  --lemma3-4 [0] = [1]
  --lemma3-4 [1] = {!!} -- blocked
  --lemma3-5 : {i : Level} {A : U i} {x y z : A} → x ≡ y ≡ z → z ≡ x ≡ y
  --lemma3-5 [0] = ? -- blocked
  --lemma3-6 : {i : Level} {A : U i} {x y z : A} → x ≡ y ≡ z → z ≡ y ≡ x
  --lemma3-6 [0] = [1]
  --lemma3-6 [1] = {!!} -- blocked

  -- It's easy to note that _≡_≡_ complements _≡_ in the sense that what cannot be constructed from a path into this higher type, can be constructed by this higher type, without case interesction. 


  lemma5 : {i : Level} {A : U i} → (x y z : A) → z ≡ x ≡ y → z ≡ x → x ≡ y
  lemma5 x y z [0] rfl = rfl
  lemma5 x y z [1] rfl = rfl
 
  
  lemma6 : {i : Level} {A : U i} → (x y z : A) → x ≡ y ≡ z → x ≡ y → x ≡ y
  lemma6 x y z s rfl = lemma5 x y z (lemma2-3-a rfl) ₁ lemma1 x y z s rfl ⁻¹
  
  lemma7 : {i : Level} {A : U i} → (x y z : A) → (s : x ≡ y ≡ z) → (p : x ≡ y) → p ≡ lemma6 x y z s p
  lemma7 x y z [0] rfl = rfl
  lemma7 x y z [1] rfl = rfl

  lemma8-a : {i : Level} {A : U i} → (x y z : A) → (p : x ≡ y) → (q : y ≡ z)  → x ≡ y ≡ z
  lemma8-a x y z rfl rfl = [0] 
  lemma8-b : {i : Level} {A : U i} → (x y z : A) → (p : x ≡ y) → (q : y ≡ z)  → x ≡ y ≡ z
  lemma8-b x y z rfl rfl = [1]
  
  lemma9 : {i : Level} {A : U i} → (x y z : A) → (p : x ≡ y) → (q : y ≡ z)  → ₁ p ⁻¹ ≡ lemma1 y z x (lemma2-2-b p) q
  lemma9 x y z rfl rfl = rfl
  lemma10 : {i : Level} {A : U i} → (x y z : A) → (p : x ≡ y) → (q : y ≡ z)  → ₁ (p ∙₁ q) ⁻¹ ≡  lemma2 y z x (lemma2-2-b p) q 
  lemma10 x y z rfl rfl = rfl

  tr : {i : Level} {A : U i} {x y z : A} → x ≡ y → x ≡ y ≡ z → y ≡ z
  tr rfl [0] = rfl
  tr rfl [1] = rfl

  tr⁻¹ : {i : Level} {A : U i} {x y z : A} → x ≡ y → x ≡ y ≡ z → z ≡ x
  tr⁻¹ rfl [0] = rfl
  tr⁻¹ rfl [1] = rfl

  theorem0 : {i : Level} {A : U i} {x y z : A} → (p : x ≡ y) → (π : x ≡ y ≡ z) → ((p ∙₁ tr p π) ∙₁ tr⁻¹ p π ) ≡ rfl
  theorem0 rfl [0] = rfl
  theorem0 rfl [1] = rfl

  theorem1 : {i : Level} {A : U i} {x y z : A} → (p : x ≡ y) → (π : x ≡ y ≡ z) → tr⁻¹ p π ≡ ₁ (p ∙₁ tr p π) ⁻¹
  theorem1 rfl [0] = rfl
  theorem1 rfl [1] = rfl

  theorem2 : {i : Level} {A : U i} {x y z : A} → (p : y ≡ x) → (π : x ≡ y ≡ z) → tr⁻¹ (₁ p ⁻¹) π ≡ ₁ ((₁ p ⁻¹) ∙₁ tr (₁ p ⁻¹) π) ⁻¹
  theorem2 rfl [0] = rfl
  theorem2 rfl [1] = rfl
  
  postulate
    𝕊 :  U lzero
    base : 𝕊
    loop : base ≡ base
    disk : loop ≡ rfl

  theorem3 : {z : 𝕊} → (π : base ≡ base ≡ z) → (p : base ≡ base) → rfl  ≡ ((p ∙₁ tr p π) ∙₁ tr⁻¹ p π )
  theorem3 [0] rfl = rfl
  theorem3 [1] rfl = rfl

  theorem4 : {z : 𝕊} → (π : base ≡ base ≡ z) → rfl  ≡ ((loop ∙₁ tr loop π) ∙₁ tr⁻¹ loop π )
  theorem4 π = theorem3 π loop
