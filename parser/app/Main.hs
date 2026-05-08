module Main where

import Parser (parseNetwork)
import Generation (generateRocq)

main :: IO ()
main = do
  let file = "model.json"

  result <- parseNetwork file

  case result of
    Nothing -> putStrLn "Failed to parse JSON"
    Just cert -> do
      writeFile "GeneratedCertificate.v" (generateRocq cert)
      putStrLn "Generated GeneratedCertificate.v"
