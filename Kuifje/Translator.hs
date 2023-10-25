{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Kuifje.Translator where 

import qualified Kuifje.Env as E
import qualified Data.Map as Map
import Kuifje.Value
import Kuifje.Parse
import Kuifje.Syntax 
import Kuifje.Expr
import Kuifje.Stmt

import Prelude hiding ((!!), return, fmap, (>>=))
import Control.Lens hiding (Profunctor)
import Data.Semigroup
import Data.Ratio
import Data.Map.Strict
import Data.List
import qualified Data.Set as DSET
import Numeric

import Language.Kuifje.Distribution
--import Kuifje.PrettyPrint 
import Language.Kuifje.PrettyPrint 
import Language.Kuifje.Semantics
import Language.Kuifje.Syntax
import Control.Applicative

import System.IO 
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr

fst2 :: (a, b) -> a
fst2 (x, _) = x

fst3 :: (a, b, c) -> a
fst3 (x, _, _) = x

snd3 :: (a, b, c) -> b
snd3 (_, x, _) = x

trd3 :: (a, b, c) -> c
trd3 (_, _, x) = x

fst4 :: (a, b, c, d) -> a
fst4 (x, _, _, _) = x

snd4 :: (a, b, c, d) -> b
snd4 (_, x, _, _) = x

trd4 :: (a, b, c, d) -> c
trd4 (_, _, x, _) = x

frt4 :: (a, b, c, d) -> d
frt4 (_, _, _, x) = x

recoverListLength :: Expr -> Expr
recoverListLength (Var idList) = (ListLength (Var idList))
recoverListLength (ListExpr list) = (RationalConst (toRational (length list)))

recoverListID :: Expr -> Expr -> Expr
recoverListID (Var idList) index = (ListElem idList index)
recoverListID (ListExpr list) index = (ListElemDirect list index)

recoverAsgn :: Expr -> Stmt -> Map.Map String Expr -> MonadValue -> (MonadValue, Map.Map String Expr)
recoverAsgn _ (Assign id expr) fCntx list =
        let newFCntx = Map.insert id expr fCntx
            monadList = concatMonadValues list (A id expr)
         in (monadList, newFCntx)

translateExecKuifje :: Stmt -> Map.Map String Expr -> MonadValue -> (MonadValue, Map.Map String Expr)
-- Sequence Statements
translateExecKuifje (Seq []) fCntx list = (list, fCntx)
translateExecKuifje (Seq ls) fCntx list = 
        let (hdRes, hdFCntx) = (translateExecKuifje (head ls) fCntx list)
            (tlRes, tlFCntx) = (translateExecKuifje (Seq (tail ls)) hdFCntx hdRes)
         in (translateExecKuifje (Seq (tail ls)) hdFCntx hdRes)
-- Assign Statements
translateExecKuifje (Assign id expr) fCntx list = recoverAsgn expr (Assign id expr) fCntx list
--translateExecKuifje (Assign id expr) fBody fCntx list = 
--        let newFCntx = Map.insert id expr fCntx
--            monadList = concatMonadValues list (A id expr)
--         in (monadList, fBody, newFCntx)
-- Support Statements
translateExecKuifje (Plusplus id) fCntx list = 
        let var = (Var id)
            one = (RationalConst 1)
            expr = (ABinary Add var one)
         in recoverAsgn expr (Assign id expr) fCntx list
translateExecKuifje (Lessless id) fCntx list = 
        let var = (Var id)
            one = (RationalConst 1)
            expr = (ABinary Subtract var one)
         in recoverAsgn expr (Assign id expr) fCntx list
-- While Statements
translateExecKuifje (Kuifje.Syntax.While e body) fCntx list =
        -- If a variable controls a loop, it is leaked to the adversary:
        let (lBody, newFCntx) = translateExecKuifje body fCntx (O e)
            monadList = concatMonadValues list (W e lBody)
         in (monadList, newFCntx)
-- For Statements
--translateExecKuifje (For index (Var idList) body) fBody fCntx list = 
translateExecKuifje (For index ls body) fCntx list =
        let iteratorID = "iterator." ++ index
            listLen = recoverListLength ls--(ListLength (Var idList))

            preCond = concatMonadValues list (A iteratorID (RationalConst (0 % 1)))
            cond = (RBinary Lt (Var iteratorID) listLen)
            postCond = (ABinary Add (Var iteratorID) (RationalConst (1 % 1)))
            
            --element = (ListElem idList (Var iteratorID))
            element = recoverListID ls (Var iteratorID)
            toAppend = [(A index element)] ++ [(A iteratorID postCond)]
            (lBody, newFCntx) = translateExecKuifje body fCntx (L toAppend)
            monadList = concatMonadValues preCond (W cond lBody)
         in (monadList, newFCntx)
-- Skip Statements
translateExecKuifje Kuifje.Syntax.Skip fCntx list = ((concatMonadValues list (M skip)), fCntx)
-- Leak Statements
translateExecKuifje (Leak e) fCntx list = ((concatMonadValues list (O e)), fCntx)
-- Vis Statements
translateExecKuifje (Vis s) fCntx list = ((concatMonadValues list (M undefined)), fCntx)
-- External Choice Statements
translateExecKuifje (Echoice s1 s2 p) fCntx list = 
        let listTrue = (fst2 (translateExecKuifje s1 fCntx (L [])))
            listFalse = (fst2 (translateExecKuifje s2 fCntx (L [])))
            (newRes, newFCntx) = ((E listTrue listFalse p), fCntx)
            monadList = concatMonadValues list newRes
         in (monadList, newFCntx)
-- Sampling Statements
translateExecKuifje (Sampling id (Var idexp)) fCntx list =
        let exprD = getCntxExpr idexp fCntx
            expr = sampleFromDist exprD
            newFCntx = Map.insert id expr fCntx
            monadList = concatMonadValues list (A id expr)
         in (monadList, newFCntx)
translateExecKuifje (Sampling id exprD) fCntx list =
        let expr = sampleFromDist exprD
            newFCntx = Map.insert id expr fCntx
            monadList = concatMonadValues list (A id expr)
         in (monadList, newFCntx)
-- Default Value - Case a Statement is not found
translateExecKuifje stmt _ list = error ("Invalid Statement:\n" ++ (show stmt) ++ "\nList:\n" ++ (monadType list))

project :: Dist (Dist Gamma) -> Dist (Dist Rational)
project = fmap (fmap (\s -> getRational s "y"))

initGamma :: Rational -> Rational -> Gamma
initGamma x y = let g = E.add E.empty ("x", (R x)) in 
               E.add g ("y", (R y))

hyper :: Dist (Dist Rational)
hyper = let g = createMonnad (fst2 (translateExecKuifje exampelS Map.empty (L [])))
         in project $ hysem g (uniform [E.empty])

example :: String
example = "y := 0; while (x > 0) do y := x + y; x := x - 1; od;"

exampelS :: Stmt
exampelS = let (Seq ls) = parseString example 
            in Seq $ (Assign "x" (Ichoice
                        (RationalConst (5 % 1)) 
                        (RationalConst (6 % 1)) 
                        (RationalConst (1 % 2)) )):ls
