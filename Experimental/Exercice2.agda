module CDCHoTT.Experimental.Exercice2 where

open import CDCHoTT.Basics
{-open import CDCHoTT.EqualityAndPaths-}
open import Agda.Builtin.Equality
{-open import Agda.Builtin.Nat-}
open import Agda.Builtin.Float renaming (primFloatMinus to _-_)
open import Agda.Builtin.Float renaming (primFloatPlus to _+_)
open import Agda.Builtin.Float renaming (primFloatTimes to _⋆_)
open import Agda.Builtin.Float renaming (primFloatDiv to _/_)


X = Float
a = 1.0
b = 0.0
c = 1.0

f : X → X
f x = ((a ⋆ (x ⋆ x)) + ((b ⋆ x) + c))

g : X → X
g x = 0.0

Deg2Eq : Float → Float → Float → Float
Deg2Eq a b c = ((0.0 - b) + primFloatSqrt ((b ⋆ b) - (4.0 ⋆ (a ⋆ c)))) / (2.0 ⋆ a)

sol : Σ (X × X) (λ v → f (π₁ v) ≡ g (π₂ v))
sol = (Deg2Eq a b c , 0.0) , refl 

