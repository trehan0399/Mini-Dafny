module Main where

-- Make sure you run this via `stack run` in the top-level folder.
-- If you run it from `src` or `test` the tests won't be able to 
-- locate the files.


import Syntax
import Printer
import DafnyParser
import WP
import Z3

import Control.Monad
import System.Environment

main :: IO ()
main = do
  a <- getArgs
  s <- parseDafnyFile (head a)
  case s of
    Left err -> error err
    Right p -> do
      vcs <- forM (zip [1..] (vc p)) $ \(i,vcp) -> convertAndCheck vcp (head a ++ show i ++ ".smt2")
--        putStrLn $ pretty vcp
--        putStrLn $ show vcp        
      if and vcs then
        putStrLn "Program verified!"
      else
        putStrLn "FAILURE TO VERIFY"





