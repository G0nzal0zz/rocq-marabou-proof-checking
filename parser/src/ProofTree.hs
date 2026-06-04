{-# LANGUAGE DuplicateRecordFields #-}

module ProofTree where

import Parser
import Split (Split, matchSplit)

--

-- type t =
--   (*  left child, right child *)
--   | Node of Split.t * t * t
--   (* contradiction vector *)
--   | Leaf of real list

data ProofTree
  = Node Split ProofTree ProofTree -- (*  left child, right child *)
  | Leaf Tableau -- (* contradiction vector *)

-- \| Leaf [Int] -- (* contradiction vector *)

buildProofTree :: Proof -> [Constraint] -> Maybe ProofTree
buildProofTree Proof {children = ch, contradiction = contra} cons =
  case (ch, contra) of
    (Just _, Just _) ->
      Nothing
    (Nothing, Nothing) ->
      Nothing
    (Just (Children [c1, c2]), Nothing) ->
      Just (Node splitVal left right)
      where
        splitVal = matchSplit (split c1) (split c2) cons
        left = buildProofTreeChild c1 cons
        right = buildProofTreeChild c2 cons
    (Just _, Nothing) ->
      Nothing -- wrong number of children
    (Nothing, Just contra) ->
      Just $ Leaf contra

buildProofTreeChild :: Child -> [Constraint] -> ProofTree
buildProofTreeChild Child {children = ch, contradiction = contra} cons =
  case (ch, contra) of
    (Just (Children [c1, c2]), Nothing) ->
      Node splitVal left right
      where
        splitVal = matchSplit (split c1) (split c2) cons
        left = buildProofTreeChild c1 cons
        right = buildProofTreeChild c2 cons
    (Nothing, Just c) ->
      Leaf c
    _ ->
      error "Invalid child"
