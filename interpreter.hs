{-
-- Module Interpreter:  functions to interpret haskell code
-- Author: Abdul Rahim Nizamani, ITIT, Gothenburg University, Sweden
-- Started: 2013-08-23
-- Updated: 2013-09-28
-}

module Interpreter where

import Instances
import Data.Graph.AStar
import Haskell
import Language.Haskell.Parser
import Language.Haskell.Syntax
import qualified Language.Haskell.Pretty as P
import Niz
import Data.Either
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (fromJust)
import Debug.Trace
import Data.Maybe
import Control.Exception
import Data.List


type StateD = (Either String (HsExp,Maybe Axiom), [HsExp])


showState :: StateD -> String
showState (Left s, _) = s
showState (Right (exp,Nothing), _) = showExp exp
showState (Right (exp,Just d), _) = showExp exp ++ " using " ++ showAxiom d

solveAnswer :: Int -> Int -> [Axiom] -> StateD -> Maybe HsExp -> IO (Maybe HsExp)
solveAnswer width depth mod start end = do
    result <- aStarM (expandNode mod width depth)
                        stateDist hDist (isGoal end) (return start)
    if isNothing result
    then return Nothing
    else do
    let result' = fromJust result
    if null result'
    then return Nothing
    else do
    let (ans, _) = last $ fromJust result
    return $ getAnswer ans

solve :: Int -> Int -> [Axiom] -> StateD -> (Maybe HsExp) -> IO ((Maybe [StateD]))
solve width depth mod start end = do
    result <- aStarM (expandNode mod width depth)
                        stateDist hDist (isGoal end) (return start)
    return result

getAnswer (Left _) = Nothing
getAnswer (Right (r,_)) = Just r

varBindings :: Axiom -> [(HsName,HsExp)]
varBindings ((HsVar (UnQual name)) :->> exp) = [(name,exp)]
varBindings (exp :-> (HsVar (UnQual name))) = [(name,exp)]
varBindings _ = []

isGoal :: Maybe HsExp -> StateD -> IO Bool
isGoal _ (Left _, _) = return True
isGoal (Just exp) (Right (r,_), _) = do
    --putStrLn $ show r ++ "\n" ++ show exp ++ "\n" ++ show (equalExp (r, exp)) ++ "\n\n"
    --putStrLn $ P.prettyPrint r ++ "==" ++ P.prettyPrint exp ++ " = " ++ show (equalExp (r, exp)) ++ "\n\n"
    return $ equalExp (r, exp)
isGoal Nothing (Right (r,_), _) = do
        let g = isSolved r
        return g

stateDist ::  StateD -> StateD -> IO Int
stateDist _ _ = return 1

hDist :: StateD -> IO Int
hDist _ = return 1

expandNode :: [Axiom] -> Int -> Int -> StateD -> IO (Set StateD)
expandNode m _ maxLength (_, prev) | length prev >= maxLength = return Set.empty
expandNode m maxSize maxLength (Right (exp,_), prev) = do
                                      r' <- interpreter True m exp
                                      --putStrLn $ "\n   Exp: " ++ showExp exp ++ "\n"
                                      --putStrLn $ unlines $ map show $ nub [r |Right r <- r']
                                      let prev' = (exp:prev)
                                      let right = [Right (x,d) | (Right (x,d)) <- r', size x <= maxSize, not (x `elem` prev)]
                                      let left = [Left x | Left x <- r']
                                      if null right
                                      then return $ Set.fromList $ zip left (repeat prev')
                                      else do
                                      --mapM (putStrLn . pretty) $ [r | (Right r) <- right]
                                      --putStrLn $ "\n\n"
                                      return $ Set.fromList $ zip right (repeat prev')
expandNode _ _ _ (Left l, _) = return $ Set.empty
    
-- | Interprets any haskell expression from the given module
-- Only produces a single step
-- if argument indicates if it is the first level (False if in recursion mode)
interpreter :: Bool -> [Axiom] -> HsExp -> IO [Either String (HsExp,Maybe Axiom)]
-- Literal
interpreter b axioms e@(HsLit (HsString s)) = do
        let result1 = map (\x -> Right (x,Nothing)) [e, HsList (map (\c -> HsLit (HsChar c)) s)]
        let result2 = map Right $ concatMap (\x -> matchFuncArgs b x e) axioms
        return $ result1 ++ result2
interpreter b axioms e@(HsLit c) = do
        let exp' = concatMap (\x -> matchFuncArgs b x e) $ axioms
        let exp = map Right exp'
        return exp

-- Parenthesized expression
interpreter _ m (HsParen exp) = do r <- interpreter False m exp
                                   return $ [Right (HsParen e,d) | Right (e,d) <- r] ++ r

-- Negative expression
interpreter _ m (HsNegApp exp) = do r <- interpreter False m exp
                                    return [Right (HsNegApp e,d) | Right (e,d) <- r]

-- Tuple of expressions
interpreter _ _ (HsCon (Special HsUnitCon)) = return [Right (HsTuple [], Nothing) ]
interpreter b axioms e@(HsCon con) = do
        let exp' = concatMap (\x -> matchFuncArgs b x e) $ axioms
        let exp = map Right exp'
        return exp
interpreter _ _ e@(HsTuple [])  = return [Right (e,Nothing)]
interpreter _ m e@(HsTuple [x]) = do
            r' <- interpreter False m x
            let r = rights r'
            if notnull r
                then return $ map (\(x,d) -> Right (HsTuple [x] ,d) ) r
                else return $  [Left $ head $ lefts r']
            
interpreter _ m (HsTuple (x:xs)) = do
        x' <- interpreter False m x
        if notnull x' && all isLeft x'
          then return x'
          else do
            let r = [Right (HsTuple (a:xs),d) | (Right (a,d)) <- x', a /= x]
            if notnull r
            then return r
            else do
              xs' <- interpreter False m (HsTuple xs)
              let result = [Right (HsTuple (a:xsnew),d) | (Right (HsTuple xsnew,d)) <- xs', (Right (a,_)) <- x']
              if notnull result
                then return result
                else return xs'
              -- r <- construct m list
              --return $ map (Right . HsTuple) r

-- List of expressions
interpreter b axioms e@(HsList [x]) = do
            r' <- interpreter False axioms x
            let r = [Right (HsList [a],d) | Right (a,d) <- r']
            let exp' = concatMap (\x -> matchFuncArgs b x e) $ axioms
            let exp = map Right exp' -- [Right e' | e'@(HsList (e:es)) <- exp']
            if null r && null exp
                then return [Right (e,Nothing)]
                else return $ r ++ exp
interpreter b axioms e@(HsList (x:xs)) = do
        x' <- interpreter False axioms x
        let r = [Right (HsList (a:xs),d) | (Right (a,d)) <- x', a /= x]
        --putStrLn $ show x
        --putStrLn $ show (length r)
        --putStrLn $ unlines $ [show e | (Right (e,d)) <- x', e /= x]
        xs' <- interpreter False axioms (HsList xs)
        let newxs = [Right (HsList (x:xsnew),d) | (Right (HsList xsnew,d)) <- xs']
        
        let exp' = concatMap (\x -> matchFuncArgs b x e) $ axioms
        let exp = map Right exp' -- [Right e' | e'@(HsList (e:es)) <- exp']
        
        let result = r ++ exp ++ newxs
        if notnull result
        then return result
        else return [Right (e,Nothing)]
interpreter b axioms e@(HsList _) = do
        let exp' = concatMap (\x -> matchFuncArgs b x e) $ axioms
        let exp = map Right exp' -- [Right e' | e'@(HsList (e:es)) <- exp']
        if null exp
            then return [Right (e,Nothing)]
            else return $ exp
-- Wildcard
interpreter _ _ (HsWildCard) = return [Right (HsWildCard,Nothing)]

-- Variable
interpreter _ axioms (HsVar (UnQual c)) = do
    let bind' = concatMap varBindings axioms
    let bind = filter (\(x,y) -> x == c) bind'
    if null bind
        then return [] -- [Left $ "Not in scope: '" ++ prettyPrint c ++ "'"]
    else do
        let (name,exp) = last bind
        return [Right (exp,Nothing)]
interpreter _ _ (HsVar (Qual _ _)) = return [Left "Qualified variable names not supported."]
interpreter _ _ (HsVar (Special _)) = return [Left "Special variable names not supported."]
-- Function application
-- recursive application of the same function not allowed, e.g. f (f x)
interpreter b axioms func@(HsApp f arg@(HsApp g _)) | f == g = return []

interpreter b axioms func@(HsApp f@(HsApp _ _) arg) = do
            func' <- interpreter False axioms f
            arg'  <- interpreter False axioms arg
            let exp = concatMap (\x -> matchFuncArgs b x func) axioms
            let fnew = map (\(anew,d) -> Right (HsApp f anew,d)) [(r,d) | (Right (r,d)) <- arg', r /= arg]
            if null (rights func')
            then if notnull fnew
                    then return $ fnew ++ [Right e | e <- exp]
                    else if null exp
                            then return func'
                            else return [Right e | e <- exp]
            else do
                 let result = [Right (HsApp r arg,d) | (Right (r,d)) <- func', r /= f]
                 return $ result ++ fnew ++ [Right e | e <- exp]
                 --return [Left $ "Function application " ++ show func' ++ " arg: " ++ show arg]
interpreter b axioms func@(HsApp fname arg) = do
      let bind = [d | d@(m :->> _) <- axioms, matchExpExp m func]
                 ++ [d | d@(m :-> _) <- axioms, matchExpExp m func]
      arg' <- interpreter False axioms arg
      --putStrLn $ "Interpreter: " ++ (unlines $ map show bind)
      if null bind && null arg'
      then return []
      else do
        let exp = concatMap (\x -> matchFuncArgs b x func) $ bind
        let argnew = [Right (HsApp fname r, d) | (r,d) <- rights arg', r /= arg]
        if null argnew
          then if null exp
                then return []
                else return $ [Right e | e <- exp]
          else if null exp
                then return argnew
                else return $ [Right e | e <- exp] ++ argnew
-- Infix applications
interpreter b axioms func@(HsInfixApp e1 op@(HsQVarOp (UnQual opname)) e2) = do
    e1' <- interpreter False axioms e1
    e2' <- interpreter False axioms e2
    qual <- prelude func
    let e1new = [Right ((HsInfixApp x op e2),d) | (Right (x,d)) <- e1', x /= e1]
    let e2new = [Right ((HsInfixApp e1 op x),d) | (Right (x,d)) <- e2', x /= e2]
    let enew = e1new ++ e2new ++ map (\(Right x) -> Right (x,Nothing)) qual
    let exps = concatMap (\x -> matchFuncArgs b x func) axioms
    
    -- putStrLn $ "Interpreter: " ++ (unlines $ map show exps)
    
    if null exps -- $trace (unlines $ map P.prettyPrint exps) exps
        then return enew -- [Left $ "Incomplete function definition for " ++ prettyPrint opname]
        else return $ [Right e | e <- exps] ++ enew
interpreter b axioms func@(HsInfixApp e1 op@(HsQConOp (UnQual opname)) e2) = do
    e1' <- interpreter False axioms e1
    e2' <- interpreter False axioms e2
    qual <- prelude func
    let e1new = [Right ((HsInfixApp x op e2),d) | (Right (x,d)) <- e1', x /= e1]
    let e2new = [Right ((HsInfixApp e1 op x),d) | (Right (x,d)) <- e2', x /= e2]
    let enew = e1new ++ e2new ++ map (\(Right x) -> Right (x,Nothing)) qual

    let exps = concatMap (\x -> matchFuncArgs b x func) axioms
    if null exps
        then return enew -- [Left $ "Incomplete function definition for " ++ prettyPrint opname]
        else return $ [Right e | e <- exps] ++ enew

interpreter b m (HsInfixApp e1 op (HsParen e2)) = interpreter b m (HsInfixApp e1 op e2)
interpreter b m (HsInfixApp (HsParen e1) op e2) = interpreter b m (HsInfixApp e1 op e2)
interpreter _ m (HsInfixApp c@(HsLit (HsChar e1)) (HsQConOp (Special HsCons)) (HsList [])) = do
    return $ map (\x -> Right (x,Nothing)) [HsLit (HsString [e1]), HsList [c]]
interpreter _ m (HsInfixApp (HsLit (HsChar e1)) (HsQConOp (Special HsCons)) (HsLit (HsString e2))) = do
    return [Right (HsLit (HsString (e1:e2)),Nothing)]
interpreter _ m (HsInfixApp e1 (HsQConOp (Special HsCons)) (HsList e2)) = do
    return [Right (HsList (e1:e2),Nothing)]
interpreter _ m (HsInfixApp e1 (HsQConOp opname) e2) =
    return [] -- [Left $ "Constructor operators not supported yet. " ++ prettyPrint opname]

-- interpreter _ _ _ = return []

-- Unsupported expression types
--interpreter _ _ (HsApp (HsLit _) _) = return [Left "Function name cannot be a literal."]
--interpreter _ _ (HsApp _ _) = return [Left "Unknown function type."]

-- Unimplemented expression types
--interpreter _ _ (HsCon _)            = return [Left "Data constructors not supported yet."]
--interpreter _ _ (HsInfixApp _ _ _)   = return [Left "Infix applications not supported yet."]
interpreter _ _ (HsLambda _ _ _)     = return [Left "Lambda applications not supported yet."]
interpreter _ _ (HsLet _ _)          = return [Left "Let expression not supported yet."]
interpreter _ _ (HsIf _ _ _)         = return [Left "If..then..else expression not supported yet."]
interpreter _ _ (HsCase _ _)         = return [Left "Case expression not supported yet."]
interpreter _ _ (HsDo _)             = return [Left "Do expression not supported yet."]
interpreter _ _ (HsLeftSection _ _)  = return [Left "Left section not supported yet."]
interpreter _ _ (HsRightSection _ _) = return [Left "Right section not supported yet."]
interpreter _ _ (HsEnumFrom _)       = return [Left "Enumeration not supported yet."]
interpreter _ _ (HsEnumFromTo _ _)   = return [Left "Enumeration not supported yet."]
interpreter _ _ (HsEnumFromThen _ _) = return [Left "Enumeration not supported yet."]
interpreter _ _ (HsEnumFromThenTo _ _ _) = return [Left "Enumeration not supported yet."]
interpreter _ _ (HsListComp _ _)     = return [Left "List comprehension not supported yet."]
interpreter _ _ (HsExpTypeSig _ _ _) = return [Left "Type signatures not supported yet."]
interpreter _ _ (HsAsPat _ _)        = return [Left "Patterns not supported yet."]
interpreter _ _ (HsIrrPat _)         = return [Left "Patterns not supported yet."]
--interpreter _ _ _                    = return [Left "Not supported yet."]


-- This takes an expression and evalutes it from prelude functions directly
prelude :: HsExp -> IO [Either String HsExp]
prelude func@(HsInfixApp (HsList e1) (HsQVarOp (Qual (Module "P") (HsSymbol "++"))) (HsList e2))
    = catch (return [Right (HsList (e1 ++ e2))])
            empty
        where 
            empty :: IOException -> IO [Either String HsExp]
            empty _ = return []
prelude func@(HsInfixApp (HsList e1) (HsQVarOp (Qual (Module "P") (HsSymbol "\\\\"))) (HsList e2))
    = catch (return [Right (HsList (e1 \\ e2))])
            empty
        where 
            empty :: IOException -> IO [Either String HsExp]
            empty _ = return []
prelude func@(HsInfixApp (HsList e1) (HsQVarOp (Qual (Module "P") (HsIdent "union"))) (HsList e2))
    = catch (return [Right (HsList (e1 `union` e2))])
            empty
        where 
            empty :: IOException -> IO [Either String HsExp]
            empty _ = return []
prelude func@(HsInfixApp (HsList e1) (HsQVarOp (Qual (Module "P") (HsIdent "intersect"))) (HsList e2))
    = catch (return [Right (HsList (e1 `intersect` e2))])
            empty
        where 
            empty :: IOException -> IO [Either String HsExp]
            empty _ = return []

prelude func@(HsInfixApp (HsInfixApp e1 (HsQVarOp (Qual (Module "P") (HsSymbol "++"))) e2) (HsQVarOp (Qual (Module "P") (HsSymbol "++"))) e3)
    = return $ map Right [(HsInfixApp e1 (HsQVarOp (Qual (Module "P") (HsSymbol "++"))) (HsInfixApp e2 (HsQVarOp (Qual (Module "P") (HsSymbol "++"))) e3))]
prelude func@(HsInfixApp e1 (HsQVarOp (Qual (Module "P") (HsSymbol "++"))) (HsInfixApp e2 (HsQVarOp (Qual (Module "P") (HsSymbol "++"))) e3))
    = return $ map Right [(HsInfixApp (HsInfixApp e1 (HsQVarOp (Qual (Module "P") (HsSymbol "++"))) e2) (HsQVarOp (Qual (Module "P") (HsSymbol "++"))) e3)]
prelude _ = return []

isLeft (Left _) = True
isLeft _ = False

isRight (Right _) = True
isRight _ = False

