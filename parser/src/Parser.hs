{-# LANGUAGE DeriveGeneric #-}

module Parser (parseNetwork, ProofCertificate(..), TableauItem(..)) where

import Data.Aeson (FromJSON, decode)
import qualified Data.ByteString.Lazy as B
import GHC.Generics (Generic)
import GHC.List (List)

data TableauItem = TableauItem
  { var :: Int,
    val :: Float
  }
  deriving (Show, Generic)

instance FromJSON TableauItem

data ProofCertificate = ProofCertificate
  { tableau :: List (List TableauItem)
  }
  deriving (Show, Generic)

instance FromJSON ProofCertificate

parseNetwork :: String -> IO (Maybe ProofCertificate)
parseNetwork file = do
  content <- B.readFile file
  return $ decode content
