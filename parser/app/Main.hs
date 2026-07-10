module Main where

import Generation (generateCertificateSpecs, generateRocq)
import Options.Applicative
import Parser (ProofCertificate (constraints, proof, tableau, upperBounds), parseProofCertificates, Tableau (Tableau))
import ProofTree (buildProofTree)
import Text.Printf (printf)

data Arguments = Arguments
  { input :: String,
    output :: String,
    specsOutput :: String
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
          <> value "parsed_certificate.v"
          <> help "File where the generated Rocq data types will be placed"
      )
    <*> strOption
      ( long "specs-output"
          <> metavar "FILE"
          <> short 's'
          <> value "parsed_certificate_specs.v"
          <> help "File where the generated certificate specs will be placed"
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
      let n_val = length (upperBounds cert)
          (Tableau rows) = tableau cert
          rowCount = length rows
      in case buildProofTree (proof cert) (constraints cert) n_val rowCount of
        Nothing ->
          putStrLn "Error while generating Proof Tree"
        Just tree -> do
          writeFile (output args) (generateRocq cert tree)
          printf "Generated %s\n" (output args)
          writeFile (specsOutput args) (generateCertificateSpecs n_val (rowCount - 2))
          printf "Generated %s\n" (specsOutput args)
  where
    opts =
      info
        (arguments <**> helper)
        ( fullDesc
            <> header
              "A helper Haskell program to convert Marabou proof certificates into Rocq data types for validation."
        )
