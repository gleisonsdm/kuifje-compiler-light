module Kuifje.Run where

import Kuifje.Stmt
import Kuifje.Translator
import Kuifje.LivenessAnalysis
import Kuifje.Parse
import Kuifje.Value
import Kuifje.Syntax
import Kuifje.PrettyPrint 
import Kuifje.JsonPrint
import Kuifje.CsvLoader
import qualified Kuifje.Env as E

import System.Environment

import System.IO 
import Data.Map.Strict
import Data.List
import Language.Kuifje.Distribution hiding (return)
import Language.Kuifje.PrettyPrint
import Language.Kuifje.Semantics
import Language.Kuifje.Syntax
import Language.Kuifje.ShallowConsts
import Text.PrettyPrint.Boxes (printBox)
import Prelude hiding ((!!), fmap, (>>=))
import qualified Data.Map as Map

import Data.IORef

getFrom g s | Just x <- E.lookup g s = x
            | otherwise = error ("Not going to happend " ++ s)
            
project :: String -> Dist (Dist Gamma) -> Dist (Dist Value)
project var = fmap (fmap (\s -> getFrom s var))

processFlag :: String -> String -> [(String, (Dist (Dist Value)))] -> IO ()
processFlag "json1" fName values = createJson1 fName values
processFlag "json2" fName values = createJson2 fName values
processFlag f _ _ = error ("\n\n  Unknown flag:\n" ++ f ++ "\n")

readFlags :: [String] -> String -> [(String, (Dist (Dist Value)))] -> IO ()
readFlags [] fName _ = putStrLn $ ""
readFlags ls fName variables = do processFlag (head ls) fName variables
                                  readFlags (tail ls) fName variables

--runHyper :: String -> [String] -> IO ()
--runHyper s ls = do tmp <- parseFile s
--                   let m = Map.empty
--                   let e = Map.empty
--                   st <- readCSVs s tmp
--                   let l = fst3 (translateExecKuifje st m e (L []))
--                   let v = runLivenessAnalysis l
--                   let g = createMonnad l 
--                   let kuifje = hysem g (uniform [E.empty])
--                   let (env, _) = (toList $ runD kuifje) !! 0
--                   let (gamma, _) = ((toList $ runD $ env) !! 0)
--                   let all_var = E.allVar gamma
--                   writeDecimalPrecision 6
--                   if v then
--                      do let output = [(x, Kuifje.Run.project x kuifje) | x <- all_var]
--                         readFlags ls s output
--                         outputL output 
--                   else error ("\n\nCompilation fatal error.\n\n")

outputL :: (Ord a, Boxable a) => [(String, Hyper a)] -> IO ()
outputL ls =
  mapM_ (\l ->
    do
      putStrLn $ "> Variable " ++ fst l ++ " hyper"
      printBox . toBox . snd $ l
      putStrLn $ "> condEntropy bayesVuln " ++ fst l ++ " hyper"
      printBox . toBox . condEntropy bayesVuln . snd $ l
      putStrLn ""
  ) ls

compileFile filename param =
  do
    file <- parseFile filename
    let map1 = Map.empty
    st <- readCSVs filename file
    let ast =  fst2 (translateExecKuifje st map1 (L []))
    return ast

runFile :: String -> [String] -> Dist Gamma -> IO (Hyper Gamma)
runFile filename param distrib =
  do
    ast <- compileFile filename param
    let v = runLivenessAnalysis ast
    let monadAst = createMonnad ast
    if v then 
      do return (hysem monadAst distrib)
    else error ("\n\nCompilation fatal error.\n\n")

runFileDefaultParams :: String -> [String] -> IO ()
runFileDefaultParams s param =
  do
    hyper <- runFile s param (uniform [E.empty])
    let (env, _) = (toList $ runD hyper) !! 0
    let (gamma, _) = ((toList $ runD $ env) !! 0)
    let all_var = E.allVar gamma
    writeDecimalPrecision 6
    let output = [(x, Kuifje.Run.project x hyper) | x <- all_var]
    readFlags param s output
    outputL output

