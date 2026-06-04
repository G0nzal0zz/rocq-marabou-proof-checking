module Generation (generateRocq) where

import Data.List (intercalate)
import Parser (ProofCertificate (tableau), Tableau, TableauItem (val, var))

generateRocq :: ProofCertificate -> String
generateRocq cert =
  unlines
    [ "Require Import Reals.",
      "Require Import List.",
      "Require Import Util.",
      "Import ListNotations.",
      "Open Scope R_scope.",
      "",
      "",
      tableauToRocq (tableau cert) ++ "."
    ]

--- =====================================================
-- Tableau
-- =====================================================

tableauToRocq :: Tableau -> String
tableauToRocq rows =
  "[" ++ intercalate "; " (map itemToRocq rows) ++ "]"

itemToRocq :: TableauItem -> String
itemToRocq item =
  "{| var := "
    ++ show (var item)
    ++ "; val := "
    ++ show (val item)
    ++ "%R |}"

--- =====================================================
-- Tableau
-- =====================================================
