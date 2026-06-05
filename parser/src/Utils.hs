module Utils where

import Parser (TableauItem (TableauItem))

tableauToList :: Int -> [TableauItem] -> [Float]
tableauToList len items =
  if len < 0
    then []
    else tableauToList (len - 1) items ++ [lookupVar items len]

lookupVar :: [TableauItem] -> Int -> Float
lookupVar [] _ = 0
lookupVar (TableauItem var val : xs) n =
  if var == n then val else lookupVar xs n
