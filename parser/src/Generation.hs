module Generation (generateRocq) where

import Data.List (intercalate)
import Parser (ProofCertificate(tableau), TableauItem(var, val))

generateRocq :: ProofCertificate -> String
generateRocq cert =
  unlines
    [ "Require Import Reals."
    , "Require Import List."
    , "Import ListNotations."
    , "Open Scope R_scope."
    , ""
    , "Record TableauItem := {"
    , "  var : nat;"
    , "  val : R"
    , "}."
    , ""
    , "Definition certificate : list (list TableauItem) :="
    , tableauToRocq (tableau cert) ++ "."
    ]

tableauToRocq :: [[TableauItem]] -> String
tableauToRocq rows =
  "[" ++ intercalate "; " (map rowToRocq rows) ++ "]"

rowToRocq :: [TableauItem] -> String
rowToRocq row =
  "[" ++ intercalate "; " (map itemToRocq row) ++ "]"

itemToRocq :: TableauItem -> String
itemToRocq item =
  "{| var := "
    ++ show (var item)
    ++ "; val := "
    ++ show (val item)
    ++ "%R |}"
