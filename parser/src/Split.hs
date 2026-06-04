{-# LANGUAGE DataKinds #-}

module Split where

import Parser (Constraint (..), RawSplit (..))

-- type t =
--     SingleSplit of int * real (* variable, value *)
--     | ReluSplit of int * int * int (* participating relu variables: b, f, aux *)

data Split
  = SingleSplit Int Float -- (* variable, value *)
  | ReluSplit Int Int Int -- (* participating relu variables: b, f, aux *)

-- (* check that some split corresponds to a single variable split *)
-- let match_single_var_split (l_t: Tightening.t list) (r_t: Tightening.t list): t option =
--     match l_t, r_t with
--     | [(var1, value1, UPPER)], [(var2, value2, LOWER)]
--     | [(var1, value1, LOWER)], [(var2, value2, UPPER)] ->
--         if var1 = var2 && value1 = value2
--         then Some (SingleSplit (var1, value1))
--         else None
--     | _, _ -> None
--

matchSingleSplit :: [RawSplit] -> [RawSplit] -> Maybe Split
matchSingleSplit [RawSplit var1 value1 "U"] [RawSplit var2 value2 "L"] =
  if var1 == var2 && value1 == value2
    then Just (SingleSplit var1 value1)
    else Nothing
matchSingleSplit [RawSplit var1 value1 "L"] [RawSplit var2 value2 "U"] =
  if var1 == var2 && value1 == value2
    then Just (SingleSplit var1 value1)
    else Nothing
matchSingleSplit _ _ = Nothing

-- (* check that the split corresponds to the active phase of a ReLU constraint *)
-- let is_active tightening b aux = match tightening with
--     | [(var1, 0., UPPER); (var2, 0., LOWER)] -> var1 = aux && var2 = b
--     | [(var1, 0., LOWER); (var2, 0., UPPER)] -> var1 = b && var2 = aux
--     | _ -> false

isActive :: [RawSplit] -> Int -> Int -> Bool
isActive split b aux = case split of
  [RawSplit var1 0.0 "U", RawSplit var2 0.0 "L"] -> var1 == aux && var2 == b
  [RawSplit var1 0.0 "L", RawSplit var2 0.0 "U"] -> var1 == b && var2 == aux
  _ -> False


-- (* check that the split corresponds to the inactive phase of a ReLU constraint *)
-- let is_inactive tightening f b = match tightening with
--     | [(var1, 0., UPPER); (var2, 0., UPPER)] -> (var1 = f && var2 = b) || (var1 = b && var2 = f)
--     | _ -> false

isInactive :: [RawSplit] -> Int -> Int -> Bool
isInactive split f b = case split of
  [RawSplit var1 0.0 "U", RawSplit var2 0.0 "U"] -> (var1 == f && var2 == b) || (var1 == b && var2 == f)
  _ -> False

-- (* check if given tightenings correspond to a relu split on the given variables *)
-- let is_relu_split b f aux l_tightenings r_tightenings: bool =
--     match l_tightenings, r_tightenings with
--     [(x1, 0., t1); (x2, 0., t2)], [(x3, 0., t3); (x4, 0., t4)] -> (
--         (is_active l_tightenings b aux && is_inactive r_tightenings f b) ||
--         (is_inactive l_tightenings f b && is_active r_tightenings b aux))
--         | _ ->  false

-- TODO: Complete function
isReluSplit :: [RawSplit] -> [RawSplit] -> Int -> Int -> Int -> Bool
isReluSplit lSplit rSplit b f aux = case (lSplit, rSplit) of
  ([RawSplit _ 0.0 _, RawSplit _ 0.0 _], [RawSplit _ 0.0 _, RawSplit _ 0.0 _]) -> (isActive lSplit b aux && isInactive rSplit f b) || (isInactive lSplit f b && isActive rSplit b aux)
  _ -> False

matchReluSplit :: [RawSplit] -> [RawSplit] -> [Constraint] -> Maybe Split
matchReluSplit _ _ [] = Nothing
matchReluSplit lSplit rSplit (Constraint 0 (b : f : aux : _) : xs) =
  if isReluSplit lSplit rSplit b f aux
    then Just (ReluSplit b f aux)
    else matchReluSplit lSplit rSplit xs
matchReluSplit lSplit rSplit (_ : xs) =
  matchReluSplit lSplit rSplit xs

matchSplit :: [RawSplit] -> [RawSplit] -> [Constraint] -> Split
matchSplit lSplit rSplit cons = case matchSingleSplit lSplit rSplit of
  Just singleSplit -> singleSplit
  Nothing -> case matchReluSplit lSplit rSplit cons of
    Just reluSplit -> reluSplit
    _ -> error "Could not match split"
