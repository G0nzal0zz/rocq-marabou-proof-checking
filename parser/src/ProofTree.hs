{-# LANGUAGE DuplicateRecordFields #-}

module ProofTree where

import Parser
import Split (Split, matchSplit)
import Utils (tableauToList)

-- type t =
--   (*  left child, right child *)
--   | Node of Split.t * t * t
--   (* contradiction vector *)
--   | Leaf of real list

data ProofTree
  = Node Split ProofTree ProofTree -- (*  left child, right child *)
  | Leaf [Float] -- (* contradiction vector *)


buildProofTree :: Proof -> [Constraint] -> Int -> Maybe ProofTree
buildProofTree Proof {children = ch, contradiction = contra} cons tableauWidth =
  case (ch, contra) of
    (Just _, Just _) ->
      Nothing
    (Nothing, Nothing) ->
      Nothing
    (Just (Children [c1, c2]), Nothing) ->
      Just (Node splitVal left right)
      where
        splitVal = matchSplit (split c1) (split c2) cons
        left = buildProofTreeChild c1 cons tableauWidth
        right = buildProofTreeChild c2 cons tableauWidth
    (Just _, Nothing) ->
      Nothing -- wrong number of children
    (Nothing, Just contra) ->
      Just $ Leaf (tableauToList tableauWidth contra)

buildProofTreeChild :: Child -> [Constraint] -> Int -> ProofTree
buildProofTreeChild Child {children = ch, contradiction = contra} cons tableauWidth =
  case (ch, contra) of
    (Just (Children [c1, c2]), Nothing) ->
      Node splitVal left right
      where
        splitVal = matchSplit (split c1) (split c2) cons
        left = buildProofTreeChild c1 cons tableauWidth
        right = buildProofTreeChild c2 cons tableauWidth
    (Nothing, Just contra) ->
      Leaf (tableauToList tableauWidth contra)
    _ ->
      error "Invalid child"
