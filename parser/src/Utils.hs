module Utils where

import Data.Ratio ((%))

import Parser (TableauItem (TableauItem), Tableau (Tableau))

tableauToList :: Int -> [TableauItem] -> [Rational]
tableauToList len items =
  if len < 0
    then []
    else tableauToList (len - 1) items ++ [lookupVar items len]

lookupVar :: [TableauItem] -> Int -> Rational
lookupVar [] _ = 0 % 1
lookupVar (TableauItem var val : xs) n =
  if var == n then val else lookupVar xs n

tableauToDenseRows :: Tableau -> Int -> [[Rational]]
tableauToDenseRows (Tableau rows) n_val =
  map (\row -> tableauToList (n_val - 1) row) rows
