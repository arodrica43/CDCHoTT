module CDCHoTT.Experimental.Exercice1 where

open import CDCHoTT.Basics
{-open import CDCHoTT.EqualityAndPaths-}
{-open import Agda.Builtin.Equality-}
{-open import Agda.Builtin.Nat-}
open import Agda.Builtin.Float renaming (primFloatMinus to _-_)
open import Agda.Builtin.Float renaming (primFloatPlus to _+_)
open import Agda.Builtin.Float renaming (primFloatTimes to _⋆_)
open import Agda.Builtin.Float renaming (primFloatDiv to _/_)
open import Agda.Builtin.Float renaming (primFloatEquality to _≡_)
open import Agda.Builtin.Bool renaming (Bool to PBool)



{-
Nat² =  Nat × Nat
lema : (x y : Nat) →  π₁ (x , (x + y)) ≈ π₂ (x , (x + y)) + y
lema = {!!}

solution : (x : Nat) → Σ Nat² λ z → π₁ z ≈ π₂ z + 2
solution x = (x , (x + 2)) , lema x 2
-}


{-
f : Nat → Nat
f x = x - x * x
sol1 : Σ Nat λ x → f x ≡ zero
sol1 = 0 , refl
sol2 : Σ Nat λ x → f x ≡ zero
sol2 = 1 , refl
sol3 : Σ Nat λ x → f x ≡ zero
sol3 = 2 , refl
sol4 : Σ Nat λ x → f x ≡ zero
sol4 = 19123 , refl

negatives-are-zero : 0 - 1 ≡ 0
negatives-are-zero = refl
-}

{-
g : Float → Float
g x = x 

sol1 : Σ Float λ x → g x ≡ 0.0
sol1 = 1e-323 , refl

sol2 : Σ Float λ x → g x ≡ 0.0
sol2 = 1e-324 , refl
-}

{-
F : (Float → Float) → (Float → Float)
F f x = f x - (x ⋆ x)

f₀ : Float → Float
f₀ x = 0.0

h : Float → Float
h x = (x ⋆ x)

p : Float
p = 0.0

sol1 : Σ Float λ x → Σ (Float → Float) λ f → F f x ≡ 0.0 
sol1 = p , (h , refl)
-}

Equations : (X Y Z : U₀) → U₀
Equations X Y Z = (X → Z) × (Y → Z)

AllEquations = Σ (U₀ × (U₀ × U₀)) λ V → Equations (π₁ V) (π₁ (π₂ V)) (π₂ (π₂ V))
Eqs : (X : U₀) → U₀
Eqs X = Equations X X X

eqs-embedding : (X : U₀) → Eqs X → AllEquations
eqs-embedding X ϕ = (X , (X , X)) , ϕ

{-
Solutions : (α : AllEquations) → U₀
Solutions α = Σ (π₁ (Σπ₁ α)) (λ x → Σ (π₁ (π₂ (Σπ₁ α))) λ y → ((π₁ (Σπ₂ α)) x ≡ (π₂ (Σπ₂ α)) y)) 


X = Float
eq : Eqs X
eq = (λ x → x + x) , (λ y → y)
ϕ = eqs-embedding X eq
y : X → X
y x = 2.0 ⋆ x
sol : (x : X) → Solutions ϕ
sol x = x , (y x , refl)


eq₂ : Eqs X
eq₂ = (λ x → 2.0 + x) , (λ y →  0.0)
ϕ₂ = eqs-embedding X eq₂
y₂ : X → X
y₂ x = -2.0
sol₂ : (x : X) → Solutions ϕ₂
sol₂ x = y₂ x , (0.0 , refl)

-}

is-solution : (α : Eqs Float) → (x y : Float) → PBool
is-solution α = λ x y → (π₁ α) x ≡ (π₂ α) y

eq : Eqs Float
eq = (λ x → x + x) , (λ y → y)

y : Float → Float
y x = 2.0 ⋆ x

postulate x : Float

p : Σ Float λ x → (Σ Float λ y → PBool)
p = x , (y x , is-solution eq x (y x))

check_solution : Float → PBool
check_solution x = is-solution eq x (y x)

{-# COMPILE GHC check_solution as check_solution #-}
                                         

