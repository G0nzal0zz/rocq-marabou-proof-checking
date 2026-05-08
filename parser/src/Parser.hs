{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Parser (parseProofCertificatesEither, ProofCertificate (..), TableauItem (..), ProofItem(..)) where

import Data.Aeson (FromJSON, eitherDecode)
import qualified Data.ByteString.Lazy as B
import GHC.Generics (Generic)

data TableauItem = TableauItem
  { var :: Int,
    val :: Float
  }
  deriving (Show, Generic)

instance FromJSON TableauItem

data ConstraintItem = ConstraintItem
  { constraintType :: Int,
    vars :: [Int]
  }
  deriving (Show, Generic)

instance FromJSON ConstraintItem

data SplitItem = SplitItem
  { var :: Int,
    val :: Float,
    bound :: String
  }
  deriving (Show, Generic)

instance FromJSON SplitItem

data LemmasItem = LemmasItem
  { affVar :: Int,
    affBound :: String,
    bound :: Float,
    causVar :: Int,
    causBound :: String,
    constraint :: Int,
    expl :: [TableauItem]
  }
  deriving (Show, Generic)

instance FromJSON LemmasItem

data ChildrenItem = ChildrenItem
  { split :: [SplitItem],
    lemmas :: Maybe [LemmasItem],
    children :: Maybe [ChildrenItem],
    contradiction :: Maybe [TableauItem]
  }
  deriving (Show, Generic)

instance FromJSON ChildrenItem

data ProofItem = ProofItem
  { children :: [ChildrenItem]
  }
  deriving (Show, Generic)

instance FromJSON ProofItem

data ProofCertificate = ProofCertificate
  { tableau :: [[TableauItem]],
    lowerBounds :: [Float],
    upperBounds :: [Float],
    constraints :: [ConstraintItem],
    proof :: ProofItem
  }
  deriving (Show, Generic)

instance FromJSON ProofCertificate

parseProofCertificatesEither :: String -> IO (Either String ProofCertificate)
parseProofCertificatesEither  file = do
  content <- B.readFile file
  return $ eitherDecode content
