module Main where

import Generation (generateRocq)
import Options.Applicative
import Parser (ProofCertificate (..), ProofItem (..), parseProofCertificates)
import Text.Printf (printf)

data Sample = Sample
  { input :: String,
    output :: String
  }

sample :: Parser Sample
sample =
  Sample
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
          <> value "Certificates.v"
          <> help "File where the generated Rocq data types will be placed"
      )

main :: IO ()
main = do
  args <- execParser opts

  result <- parseProofCertificates $ input args
  case result of
    Left err -> do
      putStrLn "Failed to parse JSON"
      putStrLn err
    Right cert -> do
      writeFile "GeneratedCertificate.v" (generateRocq cert)
      printf "Generated %s\n" (output args)
  where
    opts =
      info
        (sample <**> helper)
        ( fullDesc
            <> header "A helper Haskell program to convert Marabou proof certificates into Rocq data types for validation."
        )

-- main :: IO ()
-- main = do
--   let file = "model.json"
--
--   result <- parseProofCertificatesEither file
--
--   case result of
--     Left err -> do
--       putStrLn "Failed to parse JSON"
--       putStrLn err
--     Right cert -> do
--       -- case lowerBounds cert of
--       --     []    -> putStrLn "Empty list"
--       --     (x:_) -> print x
--       -- case upperBounds cert of
--       --     []    -> putStrLn "Empty list"
--       --     (x:_) -> print x
--       -- case constraints cert of
--       --     []    -> putStrLn "Empty list"
--       --     (x:_) -> print x
--       -- case children (proof cert) of
--       --     []    -> putStrLn "Empty list"
--       --     (x:_) -> print x
--       writeFile "GeneratedCertificate.v" (generateRocq cert)
--       putStrLn "Generated GeneratedCertificate.v"
