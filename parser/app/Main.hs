module Main where

import Generation (generateRocq)
import Options.Applicative
import Parser (ProofCertificate (constraints, proof, upperBounds), parseProofCertificates)
import ProofTree (buildProofTree)
import Text.Printf (printf)

data Arguments = Arguments
  { input :: String,
    output :: String
  }

arguments :: Parser Arguments
arguments =
  Arguments
    <$> strOption
      ( long "input"
          <> metavar "FILE"
          <> short 'i'
          <> help "File containing the proof certificates"
      )
    <*> strOption
      ( long "output"
          <> metavar "FILE"
          <> short 'o'
          <> value "certificates.v"
          <> help "File where the generated Rocq data types will be placed"
      )

main :: IO ()
main = do
  args <- execParser opts

  result <- parseProofCertificates (input args)

  case result of
    Left err -> do
      putStrLn "Failed to parse JSON"
      putStrLn err
    Right cert ->
      case buildProofTree (proof cert) (constraints cert) (length (upperBounds cert)) of
        Nothing ->
          putStrLn "Error while generating Proof Tree"
        Just tree -> do
          writeFile (output args) (generateRocq cert tree)
          printf "Generated %s\n" (output args)
  where
    opts =
      info
        (arguments <**> helper)
        ( fullDesc
            <> header
              "A helper Haskell program to convert Marabou proof certificates into Rocq data types for validation."
        )
