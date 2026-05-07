{-# LANGUAGE DeriveGeneric #-}

module Main where

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

-- Parse JSON file into Network
parseNetwork :: FilePath -> IO (Maybe ProofCertificate)
parseNetwork path = do
  content <- B.readFile path
  return (decode content)

main :: IO ()
main = do
  let file = "model.json"

  result <- parseNetwork file

  case result of
    Nothing -> putStrLn "Failed to parse JSON"
    Just net -> do
      putStrLn "Parsed network successfully:"
      print net
