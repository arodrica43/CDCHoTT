module CDCHoTT.Experimental.Hbase where

open import Agda.Builtin.Float

my_sum : Float → Float
my_sum x = primFloatPlus x x

{-# COMPILE GHC my_sum as my_sum #-}
                                         
