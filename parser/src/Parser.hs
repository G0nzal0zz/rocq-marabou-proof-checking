{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Parser (module Parser) where

import Data.Aeson (FromJSON, eitherDecode)
import qualified Data.ByteString.Lazy as B
import GHC.Generics (Generic)

data TableauItem = TableauItem
  { var :: Int,
    val :: Float
  }
  deriving (Show, Generic)

instance Data.Aeson.FromJSON TableauItem

newtype Tableau = Tableau [[TableauItem]]
  deriving (Show, Generic)

instance Data.Aeson.FromJSON Tableau

data Constraint = Constraint
  { constraintType :: Int,
    vars :: [Int]
  }
  deriving (Show, Generic)

instance Data.Aeson.FromJSON Constraint

data RawSplit = RawSplit
  { var :: Int,
    val :: Float,
    bound :: String
  }
  deriving (Show, Generic)

instance Data.Aeson.FromJSON RawSplit

data Lemma = Lemmas
  { affVar :: Int,
    affBound :: String,
    bound :: Float,
    causVar :: Int,
    causBound :: String,
    constraint :: Int,
    expl :: Tableau
  }
  deriving (Show, Generic)

instance Data.Aeson.FromJSON Lemma

data Child = Child
  { split :: [RawSplit],
    --  NOTE: lemmas are not currently needed
    -- lemmas :: Maybe [Lemma],
    children :: Maybe Children,
    contradiction :: Maybe [TableauItem]
  }
  deriving (Show, Generic)

instance Data.Aeson.FromJSON Child

newtype Children = Children [Child]
  deriving (Show, Generic)

instance Data.Aeson.FromJSON Children

data Proof = Proof
  { children      :: Maybe Children
  , contradiction :: Maybe [TableauItem]
  }
  deriving (Show, Generic)

instance Data.Aeson.FromJSON Proof where

data ProofCertificate = ProofCertificate
  { tableau :: Tableau,
    lowerBounds :: [Float],
    upperBounds :: [Float],
    constraints :: [Constraint],
    proof :: Proof
  }
  deriving (Show, Generic)

instance Data.Aeson.FromJSON ProofCertificate

parseProofCertificates :: String -> IO (Either String ProofCertificate)
parseProofCertificates file = do
  content <- B.readFile file
  return $ Data.Aeson.eitherDecode content
