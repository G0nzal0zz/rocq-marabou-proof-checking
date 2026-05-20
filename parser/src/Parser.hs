{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Parser (parseProofCertificates, ProofCertificate (..), Tableau (..), Proof (..)) where

import Data.Aeson (FromJSON, eitherDecode)
import qualified Data.ByteString.Lazy as B
import GHC.Generics (Generic)

data TableauItem = TableauItem
  { var :: Int,
    val :: Float
  }
  deriving (Show, Generic)

instance FromJSON TableauItem

data Constraint = Constraint
  { constraintType :: Int,
    vars :: [Int]
  }
  deriving (Show, Generic)

instance FromJSON Constraint

data Split = Split
  { var :: Int,
    val :: Float,
    bound :: String
  }
  deriving (Show, Generic)

instance FromJSON Split

data Lemma = Lemmas
  { affVar :: Int,
    affBound :: String,
    bound :: Float,
    causVar :: Int,
    causBound :: String,
    constraint :: Int,
    expl :: [TableauItem]
  }
  deriving (Show, Generic)

instance FromJSON Lemma

data Child = Child
  { split :: [Split],
    lemmas :: Maybe [Lemma],
    children :: Maybe [Child],
    contradiction :: Maybe [TableauItem]
  }
  deriving (Show, Generic)

instance FromJSON Child

newtype ProofTree
  = ProofTree {children :: [Child]}
  deriving (Show, Generic)

instance FromJSON ProofTree

data ProofCertificate = ProofCertificate
  { tableau :: [[TableauItem]],
    lowerBounds :: [Float],
    upperBounds :: [Float],
    constraints :: [Constraint],
    proof :: ProofTree
  }
  deriving (Show, Generic)

instance FromJSON ProofCertificate

parseProofCertificates :: String -> IO (Either String ProofCertificate)
parseProofCertificates file = do
  content <- B.readFile file
  return $ eitherDecode content
