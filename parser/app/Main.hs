module Main where

import Parser (parseProofCertificatesEither, ProofCertificate (..), ProofItem(..))
import Generation (generateRocq)

main :: IO ()
main = do
  let file = "model.json"

  result <- parseProofCertificatesEither file

  case result of
    Left err -> do
      putStrLn "Failed to parse JSON"
      putStrLn err
    Right cert -> do
      -- case lowerBounds cert of
      --     []    -> putStrLn "Empty list"
      --     (x:_) -> print x
      -- case upperBounds cert of
      --     []    -> putStrLn "Empty list"
      --     (x:_) -> print x
      -- case constraints cert of
      --     []    -> putStrLn "Empty list"
      --     (x:_) -> print x 
      -- case children (proof cert) of
      --     []    -> putStrLn "Empty list"
      --     (x:_) -> print x
      writeFile "GeneratedCertificate.v" (generateRocq cert)
      putStrLn "Generated GeneratedCertificate.v"
