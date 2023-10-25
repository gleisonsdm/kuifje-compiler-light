{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Kuifje.Stmt where 

import qualified Kuifje.Env as E
import qualified Data.Map as Map
import Kuifje.Value
import Kuifje.Parse
import Kuifje.Syntax 
import Kuifje.Expr

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

valuesToExprList :: [(Value, Rational)] -> [Expr]
valuesToExprList [] = []
valuesToExprList ls =
        let hd = head ls
            exp = valueToExpr (fst hd)
            tl = valuesToExprList (tail ls)
         in exp : tl

recoverSupportAsDistList :: [(Expr, Rational)] -> [Expr]
recoverSupportAsDistList [] = []
recoverSupportAsDistList ls = 
        let (e, r) = (head ls)
            p = (RationalConst r) 
            tp = (Tuple e p)
            tl = recoverSupportAsDistList (tail ls)
          in tp : tl

getFromDist g s | Just x <- E.lookup g s = x
                | otherwise = error ("Not going to happend " ++ s)

exec :: String -> Dist (Dist Gamma) -> Dist (Dist Value)
exec var = fmap (fmap (\s -> getFromDist s var))

data MonadValue = M (Kuifje Gamma)
           | O Expr
           | A String Expr
           | L [MonadValue]
           | C Expr MonadValue MonadValue
           | E MonadValue MonadValue Expr
           | W Expr MonadValue

monadType :: MonadValue -> String
monadType (A id e) = ("\nAssign: " ++ id ++ " =>> " ++ (show e))
monadType (M md) = ("\nM: Monad")
monadType (O e) = ("\nO: Observe")
monadType (L []) = ""
monadType (L ls) = 
     let hd = monadType (head ls)
         tl = monadType (L (tail ls))
      in ("\n[" ++ hd ++ " <> "++ tl ++ "]")
monadType (C e t f) = ("\nC: \n  T = " ++ (monadType t) ++ "\n  F = " ++ (monadType f)) 
monadType (E t f p) = ("\nE: \n  T = " ++ (monadType t) ++ "\n  F = " ++ (monadType f))
monadType (W e b) = ("\nW: \n  B = " ++ (monadType b))

concatMonadValues :: MonadValue -> MonadValue -> MonadValue
concatMonadValues (L l1) (L l2) = (L (l1 ++ l2))
concatMonadValues v (L l2) = (L (v : l2))
concatMonadValues (L l1) v = (L (l1 ++ [v]))
concatMonadValues v1 v2 = (L ([v1] ++ [v2]))

createMonnad :: MonadValue -> Kuifje Gamma
createMonnad (M m) = m
createMonnad (O e) = observe (evalE e)
createMonnad (A id expr) = 
        Language.Kuifje.Syntax.update (\s -> 
          let currS = (evalE expr) s in
            fmap (\r -> E.add s (id, r)) currS)
createMonnad (L []) = skip
createMonnad (L ls) = createMonnad (head ls) <> createMonnad (L (tail ls))
createMonnad (W e body) =
        Language.Kuifje.Syntax.while (\s -> 
                let currS = (evalE e) s in 
                    fmap (\r -> case r of (B b) -> b) currS) (createMonnad body)
createMonnad (C e s1 s2) =
        Language.Kuifje.Syntax.cond 
          (\s -> let currS = (evalE e) s in fmap (\r -> case r of (B b) -> b) currS) 
          ((observe (evalE e)) <> (createMonnad s1))
          ((observe (evalE e)) <> (createMonnad s2))
          --
          -- Leaks the conditional after choose an option
          --((createMonnad s1) <> (observe (evalE e))) 
          --((createMonnad s2) <> (observe (evalE e)))
createMonnad (E s1 s2 p) =
        Language.Kuifje.Syntax.cond
          (\s -> let p' = (evalE (Ichoice (BoolConst True) (BoolConst False) p) s)
                  in (fmap (\r -> case r of (B b) -> b)) p')
          (createMonnad s1)
          (createMonnad s2)

recoverVars :: Expr -> [String] -> [String]
recoverVars (Var id) ls = ([id] ++ ls)
recoverVars (RationalConst _) ls = ls
recoverVars (Text _) ls = ls
recoverVars (IchoicesDist list) ls = 
        if length list == 1
           then recoverVars (head list) ls
           else (recoverVars (head list) ls) ++ (recoverVars (Ichoices (tail list)) ls)
recoverVars (IchoiceDist e1 e2 _) ls = 
        let ls1 = recoverVars e1 ls
            ls2 = recoverVars e2 ls1
         in ls2
recoverVars (PowerSet _) ls = ls
recoverVars (Neg r) ls = recoverVars r ls
recoverVars (ExprIf cond e1 e2) ls = 
        let ls1 = recoverVars cond ls
            ls2 = recoverVars e1 ls1
            ls3 = recoverVars e2 ls2
         in ls3
recoverVars (ABinary _ e1 e2) ls =
        let ls1 = recoverVars e1 ls
            ls2 = recoverVars e2 ls1
         in ls2
recoverVars (Ichoice e1 e2 _) ls =
        let ls1 = recoverVars e1 ls
            ls2 = recoverVars e2 ls1
         in ls2
recoverVars (Ichoices list) ls = 
        if length list == 1
           then recoverVars (head list) ls
           else (recoverVars (head list) ls) ++ (recoverVars (Ichoices (tail list)) ls)
recoverVars (Tuple e _) ls = recoverVars e ls
recoverVars (INUchoices list) ls =
        if length list == 1
           then recoverVars (head list) ls
           else (recoverVars (head list) ls) ++ (recoverVars (Ichoices (tail list)) ls)
recoverVars (INUchoicesDist list) ls =
        if length list == 1
           then recoverVars (head list) ls
           else (recoverVars (head list) ls) ++ (recoverVars (Ichoices (tail list)) ls)
recoverVars (BoolConst _) ls =  ls
recoverVars (Not b) ls = recoverVars b ls
recoverVars (SBinary _ e1 e2) ls =
        let ls1 = recoverVars e1 ls
            ls2 = recoverVars e2 ls1
         in ls2
recoverVars (BBinary _ e1 e2) ls =
        let ls1 = recoverVars e1 ls
            ls2 = recoverVars e2 ls1
         in ls2
recoverVars (RBinary _ e1 e2) ls =
        let ls1 = recoverVars e1 ls
            ls2 = recoverVars e2 ls1
         in ls2
recoverVars (Eset _) ls = ls
recoverVars (ListExpr _) ls = ls
recoverVars (ListElem id index) ls = 
        let ls1 = recoverVars (Var id) ls
            ls2 = recoverVars index ls1
         in ls2
recoverVars (ListElemDirect _ index) ls =
        let ls1 = recoverVars index ls
         in ls1
recoverVars (ListAppend id _) ls = 
        let ls1 = recoverVars (Var id) ls
         in ls1
recoverVars (ListInsert id _ _) ls =
        let ls1 = recoverVars (Var id) ls
         in ls1
recoverVars (ListRemove id _) ls =
        let ls1 = recoverVars (Var id) ls
         in ls1
recoverVars (ListLength list) ls =
        let ls1 = recoverVars list ls
         in ls1
recoverVars (ListExtend id1 id2) ls =
        let ls1 = recoverVars (Var id1) ls
            ls2 = recoverVars (Var id2) ls1
         in ls2
recoverVars (SetIchoice e) ls = recoverVars e ls
recoverVars (SetIchoiceDist e) ls = recoverVars e ls
recoverVars (TupleExpr _) ls = ls
recoverVars (Geometric _ _ _ _) ls = ls

isSetNEmpty :: Expr -> Bool
isSetNEmpty (Eset e) = ((DSET.size e) > 0)
isSetNEmpty _ = False

addInputCntx :: String -> [String] -> [Expr] -> Stmt -> Stmt
addInputCntx fName [] [] stmt = stmt
addInputCntx fName [] _  stmt = error ("Invalid Call to " ++ fName)
addInputCntx fName _  [] stmt = error ("Invalid Call to " ++ fName)
addInputCntx fName fInputs cInputs stmt = 
        let id = (fName ++ "." ++ (head fInputs))
            expr = (head cInputs)
            nAssngStmt = (Assign id expr)
            nStmt = (appendStmtBegin nAssngStmt stmt)
        in (addInputCntx fName (tail fInputs) (tail cInputs) nStmt)

addOutputCntx :: String -> [Expr] -> String -> Stmt -> Stmt
addOutputCntx fName [] [] stmt = stmt
addOutputCntx fName [] _  stmt = error ("Invalid Call to " ++ fName)
addOutputCntx fName _  [] stmt = error ("Invalid Call to " ++ fName)
addOutputCntx fName fOutputs output stmt =
        let expr = (updateVarToCntx fName (head fOutputs))
            nAssngStmt = (Assign output expr)
            nStmt = (appendStmtEnd nAssngStmt stmt)
        in (addOutputCntx fName (tail fOutputs) (tail output) nStmt)

appendStmtBegin :: Stmt -> Stmt -> Stmt
appendStmtBegin st1 (Seq ls) = (Seq (st1 : ls))
appendStmtBegin st1 stmt = (Seq [st1, stmt])

appendStmtEnd :: Stmt -> Stmt -> Stmt
appendStmtEnd st1 (Seq ls) = (Seq (ls ++ [st1]))
appendStmtEnd st1 stmt = (Seq [stmt, st1])

updateVarToCntx :: String -> Expr -> Expr
updateVarToCntx fName (Var id) = (Var (fName ++ "." ++ id))
-- (addOutputCntx fName (tail fOutputs) (tail cOutputs) nStmt)

updateID :: String -> Stmt -> Stmt
updateID fName (Assign id expr) = (Assign (fName ++ "." ++ id) expr)
updateID fName (Sampling id expr) = (Sampling (fName ++ "." ++ id) expr)
updateID fName (For id expr body) = (For (fName ++ "." ++ id) expr body)
updateID fName e = e

ichoiceToList :: Expr -> [Expr]
ichoiceToList (IchoicesDist list) = list
ichoiceToList (Ichoices list) = list
ichoiceToList e = error ("Invalid Expresssion: " ++ (show e))

updateExpression :: String -> Expr -> Expr
updateExpression fName (Var id) = (Var (fName ++ "." ++ id))
updateExpression fName (Neg r) =
     let newr = (updateExpression fName r)
     in (Neg newr)
updateExpression fName (ExprIf cond e1 e2) =
     let newcond = (updateExpression fName cond)
         newe1 = (updateExpression fName e1)
         newe2 = (updateExpression fName e2)
     in (ExprIf newcond newe1 newe2)
updateExpression fName (ABinary op e1 e2) =
     let newe1 = (updateExpression fName e1)
         newe2 = (updateExpression fName e2)
     in (ABinary op newe1 newe2)
updateExpression fName (Ichoice e1 e2 p) =
     let newp = (updateExpression fName p)
         newe1 = (updateExpression fName e1)
         newe2 = (updateExpression fName e2)
     in (Ichoice newe1 newe2 newp)
updateExpression fName (Ichoices []) = (Ichoices [])
updateExpression fName (Ichoices ls) =
     let hd = (updateExpression fName (head ls))
         tl = (updateExpression fName (Ichoices (tail ls)))
         (Ichoices list) = tl
     in (Ichoices (hd : list))
updateExpression fName (IchoiceDist e1 e2 p) =
     let newp = (updateExpression fName p)
         newe1 = (updateExpression fName e1)
         newe2 = (updateExpression fName e2)
     in (IchoiceDist newe1 newe2 newp)
updateExpression fName (IchoicesDist []) = (Ichoices [])
updateExpression fName (IchoicesDist ls) =
     let hd = (updateExpression fName (head ls))
         tl = (updateExpression fName (Ichoices (tail ls)))
         list = ichoiceToList tl
      in (IchoicesDist (hd : list))
updateExpression fName (Tuple e p) =
     let newe = (updateExpression fName e)
     in (Tuple newe p)
updateExpression fName (INUchoices []) = (INUchoices [])
updateExpression fName (INUchoices ls) =
     let hd = (updateExpression fName (head ls))
         tl = (updateExpression fName (INUchoices (tail ls)))
         (INUchoices list) = tl
     in (INUchoices (hd : list))
updateExpression fName (BBinary op e1 e2) =
     let newe1 = (updateExpression fName e1)
         newe2 = (updateExpression fName e2)
     in (BBinary op newe1 newe2)
updateExpression fName (RBinary op e1 e2) =
     let newe1 = (updateExpression fName e1)
         newe2 = (updateExpression fName e2)
     in (RBinary op newe1 newe2)
updateExpression fName (SetIchoiceDist e) = let newExpr = (updateExpression fName e)
                                             in (SetIchoiceDist newExpr)
updateExpression fName (SetIchoice e) = let newExpr = (updateExpression fName e)
                                         in (SetIchoice newExpr) 
updateExpression fName e = e


updateStmtList :: String -> [Stmt] -> [Stmt]
updateStmtList fName [] = []
updateStmtList fName ls = (updateStmtUses fName (head ls)) : (updateStmtList fName (tail ls))

updateStmtUses :: String -> Stmt -> Stmt
updateStmtUses fName (Seq []) = (Seq [])
updateStmtUses fName (Seq ls) =
     let hd = (updateStmtUses fName (head ls))
         tl = (updateStmtUses fName (Seq (tail ls)))
         (Seq list) = tl
     in (Seq (hd : list))
updateStmtUses fName (Assign id expr) = 
     let newexpr = (updateExpression fName expr)
     in (updateID fName (Assign id newexpr))
updateStmtUses fName (Kuifje.Syntax.While e s) = 
     (Kuifje.Syntax.While (updateExpression fName e) (updateStmtUses fName s)) 
updateStmtUses fName (Kuifje.Syntax.If e s1 s2) =
     (Kuifje.Syntax.If (updateExpression fName e) (updateStmtUses fName s1) (updateStmtUses fName s2))
updateStmtUses fName (Leak e) = (Leak (updateExpression fName e))
updateStmtUses fName (Echoice s1 s2 p) =
     (Echoice (updateStmtUses fName s1) (updateStmtUses fName s2) (updateExpression fName p))
updateStmtUses fName (Sampling id expr) =
     let newexpr = (updateExpression fName expr)
     in (updateID fName (Sampling id newexpr))
updateStmtUses fName (For var (Var idSet) body) =
     let newBody = (updateStmtUses fName body)
         newIdSet = (updateExpression fName (Var idSet))
     in (updateID fName (For var newIdSet newBody))
updateStmtUses fName stmt = stmt

fromJust :: Maybe (Stmt, [String], [Expr]) -> (Stmt, [String], [Expr])
fromJust (Just a) = a
fromJust Nothing = error "Function not found."

getFuncBody :: String -> Map.Map String (Stmt, [String], [Expr]) -> (Stmt, [String], [Expr])
getFuncBody id funcBody = fromJust (Map.lookup id funcBody)

--evalCaseStmt :: Stmt -> Expr
--evalCaseStmt (CaseStmt exp stmt) = exp

getRational :: Gamma -> String -> Rational
getRational g s | Just (R t) <- E.lookup g s = t
                | otherwise = error ("Not going to happen " ++ s)

