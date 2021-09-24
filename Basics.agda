{-# OPTIONS --without-K --cubical #-}

module CDCHoTT.Basics where

open import Cubical.Foundations.Everything public
open import Cubical.Data.Unit public
    renaming (Unit to 𝟙)
    renaming (tt to ∗) 
  


-- if your agda version is < 2.4 you might have to use the following:
-- 
-- postulate  -- Universe levels
--   Level : Set
--   lzero : Level
--   lsuc : Level → Level
--   _⊔_ : Level → Level → Level
-- 
-- {-# BUILTIN LEVEL Level #-}
-- {-# BUILTIN LEVELZERO lzero #-}
-- {-# BUILTIN LEVELSUC lsuc #-}
-- {-# BUILTIN LEVELMAX _⊔_ #-}
-- 
-- instead of this line:
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public

U : (i : Level) → Set (lsuc i)
U i = Set i


U₀ = U lzero
U₁ = U (lsuc lzero)



{- 
  
  supposed to be standard names in the future:
  (one advantage is, that coverings may be called 'U'...)
-}
𝒰₀ = U₀
𝒰₁ = U₁

𝒰 = U

--Type = 𝒰

{- 
from HoTT-Agda (including following comment)

Lifting to a higher universe level

The operation of lifting enjoys both β and η definitionally.
It’s a bit annoying to use, but it’s not used much (for now).
-}

{-record Lift {i j} (A : 𝒰 i) : 𝒰 (i ⊔ j) where
  instance constructor lift
  field
    lower : A
open Lift public
-}


domain : ∀ {A B : 𝒰₀} → (A → B) → 𝒰₀
domain {A} {_} _ = A

codomain : ∀ {A B : 𝒰₀} → (A → B) → 𝒰₀
codomain {_} {B} _ = B

{-
data Bool : 𝒰₀ where
  true : Bool
  false : Bool
-}


--Π : ∀ {i j} → {A : 𝒰 i} → (P : A → 𝒰 j) → 𝒰 (i ⊔ j)
--Π {A = A} P = (a : A) → P a
{--
syntax Π (λ u → t) = (u : )

π-Π : ∀ {A : 𝒰₀} {P : A → 𝒰₀}
      → (a : A) → Π P → P a
π-Π a = λ s → s a      

_∘Π_ : ∀ {X : 𝒰₀} {A B C : X → 𝒰₀}
  → (Π x ↦ (B x → C x)) → (Π x ↦ (A x → B x))
  → Π x ↦ (A x → C x)
g ∘Π f = λ a z → g a (f a z)


infix 20 _,_
record ∑ {i j} {A : 𝒰 i} (P : A → 𝒰 j) : 𝒰 (i ⊔ j) where
  constructor _,_
  field
    a : A
    p : P a

syntax ∑ (λ u → t) = Σ u ↦ t

ι-∑ : ∀ {i} {j} {A : 𝒰 i} {P : A → 𝒰 j}
      → (a : A) → P a → ∑ P
ι-∑ a p = (a , p)

∑π₁ : ∀ {i} {j} {A : 𝒰 i} {P : A → 𝒰 j} 
  → ∑ P → A
∑π₁ (a , _) = a

∑π₁-from_ :
  ∀ {i} {j} {A : 𝒰 i} (P : A → 𝒰 j)
  → ∑ P → A
∑π₁-from P = ∑π₁

∑π₂ : ∀ {i} {j} {A : 𝒰 i} {P : A → 𝒰 j}
  → (x : ∑ P) → P (∑π₁ x)
∑π₂ (a , p) = p  

∑π₂-from_ :
  ∀ {i} {j} {A : 𝒰 i} (P : A → 𝒰 j)
  → (x : ∑ P) → P (∑π₁ x)
∑π₂-from P = ∑π₂


Σ : ∀ {i j} → (A : Type i) (P : A → Type j) → Type _
Σ _ P = ∑ P

Σπ₁ : ∀ {i} {j} {A : 𝒰 i} {P : A → 𝒰 j} 
  → Σ A P → A
Σπ₁ (a , _) = a

Σπ₂ : ∀ {i} {j} {A : 𝒰 i} {P : A → 𝒰 j}
  → (x : Σ A P) → P (Σπ₁ x)
Σπ₂ (a , p) = p  

Π-to-∑ : ∀ {A : 𝒰₀} {P : A → 𝒰₀}
         → Π P → A → ∑ P
Π-to-∑ s a = (a , s a)

infix 60 _×_

_×_ : 
  ∀ {i j} 
  → (A : 𝒰 i) → (B : 𝒰 j) → 𝒰 (i ⊔ j)
A × B = ∑ (λ (a : A) → B)

_×→_ : ∀ {A B A′ B′ : 𝒰₀} → (A → B) → (A′ → B′) → (A × A′ → B × B′)
f ×→ g = λ { (a , b) → f a , g b }

_,→_ : ∀ {X A B : 𝒰₀} → (X → A) → (X → B) → (X → A × B)
f ,→ g = λ x → (f x , g x)

π₁ : ∀ {i} {A : 𝒰 i} {B : 𝒰 i} → A × B → A
π₁ (a , b) = a

π₂ : ∀ {i} {A : 𝒰 i} {B : 𝒰 i} → A × B → B
π₂ (a , b) = b 


π₁-from_×_ : ∀ {i} (A : 𝒰 i) (B : 𝒰 i) → A × B → A
π₁-from A × B = π₁

π₂-from_×_ : ∀ {i} (A : 𝒰 i) (B : 𝒰 i) → A × B → B
π₂-from A × B = π₂

Δ : ∀ {A : 𝒰₀}
    → A → A × A
Δ a = (a , a)

swap : ∀ {A B : 𝒰₀}
       → A × B → B × A
swap (a , b) = (b , a)

data Zero : 𝒰₀ where

data 𝟙 : 𝒰₀ where 
  ∗ : 𝟙

Point = 𝟙
Pt = 𝟙

id : ∀ {i} {A : 𝒰 i} → A → A
id a = a

identity-on : (A : 𝒰₀) → A → A
identity-on A = (λ (x : A) → x)

infixr 70 _∘_
_∘_ : ∀ {i j k} {A : 𝒰 i} {B : 𝒰 j} {C : 𝒰 k} → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g(f(x))

data Two : 𝒰₀ where
  ∗₁ : Two
  ∗₂ : Two

¬_ : 𝒰₀ → 𝒰₀
¬ A = A → Zero


-}
