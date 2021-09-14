module Main where

-- file exp.hs

import MAlonzo.Code.CDCHoTT.Experimental.Hbase (my_sum)
import Numeric (showFFloat)

-- boolToString :: T -> String
-- boolToString True = "TRUE"
-- boolToString False = "FALSE"

main = do
    putStrLn (my_sum 1.0)

getFloat :: IO Double
getFloat = readLn