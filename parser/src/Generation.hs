module Generation (generateRocq) where

import Data.List (intercalate)
import Parser
import ProofTree
import Split
import Utils

-- TODO: Generate Constraints
-- TODO: Fix Tableau Generation
generateRocq :: ProofCertificate -> ProofTree -> String
generateRocq cert proofTree =
  unlines
    [ "Require Import Reals.",
      "Require Import List.",
      "Require Import Util.",
      "Import ListNotations.",
      "Open Scope R_scope.",
      "",
      "",
      -- tableauToRocq (tableau cert) tableauWidth,
      "",
      listToRocq "lower_bounds" (lowerBounds cert),
      "",
      listToRocq "upper_bounds" (upperBounds cert),
      "",
      proofTreeToRocq proofTree
    ]
  where
    tableauWidth = length $ lowerBounds cert

rocqDefinition :: String -> String -> String -> String
rocqDefinition name t value = "Definition " ++ name ++ " : " ++ t ++ " := " ++ value ++ "."

--- =====================================================
-- Tableau
-- =====================================================

-- tableauToRocq :: Tableau -> Int -> String
-- tableauToRocq tableau width = listToRocq "tableau" (tableauToList width tableau)

--- =====================================================
-- List
-- =====================================================

listToRocq :: String -> [Float] -> String
listToRocq name item = rocqDefinition name "list R" ("[" ++ intercalate "; " (map show item) ++ "]")

--- =====================================================
-- Proof Tree
-- =====================================================

splitToRocq :: Split -> String
splitToRocq (SingleSplit v x) =
  "single " ++ show v ++ " " ++ show x
splitToRocq (ReluSplit b f aux) =
  "relu " ++ show b ++ " " ++ show f ++ " " ++ show aux

proofTreeToValue :: ProofTree -> String
proofTreeToValue (Leaf xs) =
  "leaf [" ++ intercalate "; " (map show xs) ++ "]"
proofTreeToValue (Node s l r) =
  "node "
    ++ splitToRocq s
    ++ " ("
    ++ proofTreeToValue l
    ++ ") ("
    ++ proofTreeToValue r
    ++ ")"

proofTreeToRocq :: ProofTree -> String
proofTreeToRocq tree =
  rocqDefinition "tree" "proof_tree" (proofTreeToValue tree)
