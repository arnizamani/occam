{-
    Inductive program synthesis : Agent training
    Author: Abdul Rahim Nizamani, ITIT, Gothenburg University, Sweden
    Started: 2013-09-29
    Updated: 2013-09-29
-}
{-# LANGUAGE DataKinds #-}
 
module Main where
import System.Environment (getArgs, getProgName)
import Niz 
import Data.Char
import Instances
import Interpreter
import Data.List
import Data.Word
import Data.Maybe
import Language.Haskell.Syntax
import Language.Haskell.Parser
import qualified Language.Haskell.Pretty as P
import System.IO
import Haskell
import Data.Maybe (isNothing)
import Control.Monad (foldM)
import Control.Parallel.Strategies
import Debug.Trace

type Language = String
type Width = Int
type Depth = Int
type Solution = Int
type Comments = String
-- data Language = Boolean | List | Math | Logic | Stream | Analogy2 | Clause
--     deriving (Eq, Show)
data Agent = Agent Comments (Width, Depth, Solution) Language FilePath [Axiom]
type IP' = (String,String,Int)

data IP  = IP {lhs :: Lhs, rhs :: Rhs, val :: Int}

instance Size IP where
    size (IP x y _) = size x + size y

type Delta = [Axiom]
noSrc = SrcLoc "" 0 0

prettyIP :: IP -> String
prettyIP (IP p e v) = showExp p ++ " = " ++ showExp e ++ ": " ++ show v

ansatz :: Language -> [HsExp]
ansatz "List" = [HsApp (HsVar (UnQual (HsIdent "rev"))) (HsVar (UnQual (HsIdent "x"))),
               HsApp (HsVar (UnQual (HsIdent "rev"))) (HsList [] )]
ansatz "Math" = [--HsApp (HsVar (UnQual (HsIdent "f"))) (HsVar (UnQual (HsIdent "x"))),
                 --HsApp (HsVar (UnQual (HsIdent "f"))) (HsLit (HsInt 0)),
                 --HsApp (HsVar (UnQual (HsIdent "f"))) (HsInfixApp (HsVar (UnQual (HsIdent "x"))) (HsQVarOp (UnQual (HsSymbol "+"))) (HsLit (HsInt 1)))
                 HsInfixApp
                    (HsVar (UnQual (HsIdent "x")))
                    (HsQVarOp (UnQual (HsIdent "g")))
                    (HsLit (HsInt 0)),
                 HsInfixApp
                    (HsVar (UnQual (HsIdent "x")))
                    (HsQVarOp (UnQual (HsIdent "g")))
                    (HsVar (UnQual (HsIdent "y"))),
                 HsInfixApp
                    (HsVar (UnQual (HsIdent "x")))
                    (HsQVarOp (UnQual (HsIdent "g")))
                    (HsInfixApp
                        (HsVar (UnQual (HsIdent "y")))
                        (HsQVarOp (UnQual (HsSymbol "+")))
                        (HsLit (HsInt 1)))
                ]
ansatz "Analogy2" = [HsApp (HsVar (UnQual (HsIdent "f"))) (HsVar (UnQual (HsIdent "x")))]
ansatz _ = []

langUnits :: Language -> Int -> [HsExp]
langUnits "Stream" 1 = [HsVar (UnQual (HsIdent x)) | x <- ["Alice","Plays","Bob","Crawls"]]
langUnits "Math" 1 = [HsLit (HsInt x) | x <- [0..9]]
--langUnits "Math" 2 = [HsLit (HsInt x) | x <- [10..99]]
langUnits "Analogy2" 1 = [HsVar (UnQual (HsIdent "Palm")),
                        HsVar (UnQual (HsIdent "Feet")),
                        HsVar (UnQual (HsIdent "Sole"))]
langUnits "List" 1 = [HsList []]
langUnits "Clause" 1 = [HsCon (UnQual (HsIdent x)) | x <- ["A","B","C"]]
langUnits _ _ = []

langOps :: Language -> Int -> [HsExp]
langOps "List" 1 = [HsVar (UnQual (HsIdent "rev"))]
langOps "List" 2 = [HsVar (UnQual (HsSymbol "++"))]
langOps "Math" 2 = [HsVar (UnQual (HsSymbol "+"))] -- ,HsVar (UnQual (HsIdent "g")) ] -- ,HsVar (UnQual (HsSymbol "*"))]
langOps "Analogy2" 1 = [HsVar (UnQual (HsIdent "under")),HsVar (UnQual (HsIdent "f2"))]
langOps "Clause" 1 = [HsVar (UnQual (HsIdent x)) | x <- ["raven","black"]]
langOps _ _ = []

printMessage = do
    p <- getProgName
    putStrLn $ "Usage: " ++ p ++ " agent.hs"
    putStrLn $ "       where: agent.hs contains the agent description and memory"

-- | Save an agent in a file
saveAgent :: Agent -> FilePath -> IO ()
saveAgent (Agent comments (width,depth,sol) lang file axioms) filename = do
    writeFile filename comments
    appendFile filename $ "-}\n"
    appendFile filename $ unlines $ map showAxiom axioms
    appendFile filename $ "\n"


main :: IO ()
main = do
    args <- getArgs
    if length args < 1
    then printMessage
    else do
    let [agentfile] = take 1 args
    agent' <- parseAgent agentfile
    if isNothing agent'
    then do
        putStrLn $ "Error reading agent."
        return ()
    else do
    let (Just agent@(Agent c (width,depth,sol) lang file _)) = agent'
    (pos,neg) <- parseTrainingFile file
    expnew <- findDelta 0 agent neg pos
    --expnew <- trainAgent agent
    if null (fst expnew)
    then do
        --putStrLn $ "All examples solved. Nothing to learn."
        return ()
    else do
        putStrLn $ "\nLearned this rule: "
        putStrLn . unlines . map showAxiom $ fst expnew
        putStrLn . show $ snd expnew
        putStrLn $ "Do you want the agent to remember it? (Y/n) "
        c <- getChar
        if c == 'n' || c == 'N'
        then do
        return ()
        else do
        let (Agent c (width,depth,sol) lang file axioms) = agent
        let newltm = union axioms (fst expnew)
        let newagent = Agent c (width,depth,sol) lang file newltm
        saveAgent newagent agentfile
        putStrLn $ "Stored in memory."
        
findDelta :: Int -> Agent -> [IP] -> [IP] -> IO ([Axiom],Int)
findDelta len ag _ _ | len < 0 = return ([],0)
findDelta len agent neg posex = do
    let (Agent c (width,depth,sol) lang file ltm) = agent
    let pos = [x  |  x@(IP p e v) <- posex,
                     e /= HsVar (UnQual (HsIdent "x"))]
    let ded = [x  |  x@(IP p (HsVar (UnQual (HsIdent "x"))) v) <- posex]
    let posAxioms = [p :->> e | IP p e v <- pos]
    let optimum   = sum ([v | IP p e v <- pos, v > 0] ++ [v | IP p e v <- ded, v > 0])
    
    if optimum < 1
    then return ([],0)
    else do
    
    if len > sum (map size pos)
    then do putStrLn $ "Size exceeded from " ++ show (sum (map size pos))
            return (posAxioms,sum [v | (IP _ _ v) <- pos, v > 0])
    else do
    if len > fromIntegral sol
    then do putStrLn $ "Maximum size reached: " ++ show sol
            return ([],0)
    else do
    if len < 1
    then do
        ans <- mapM (findAnswerDecl ltm width depth) pos
        if and ans && not (null ans)
        then do 
            newans <- mapM (findSolDecl ltm width depth) pos
            putStrLn $ "Computations1: "
            putStrLn $ unlines $ map (\x -> unlines $ map showState x) newans
            putStrLn $ "All examples solved. Nothing to learn.\n"
            return ([],0)
        else do
            newans <- mapM (findSolDecl ltm width depth) ded
            let lefts = [x | x@(Left _) <- (map fst (map head newans))]
            if null lefts && (not . null) ded
            then do
                putStrLn $ "Computations2: "
                putStrLn $ unlines $ map (\x -> unlines $ map showState x) newans
                putStrLn $ "All examples solved. Nothing to learn.\n"
                return ([],0)
            else findDelta 1 agent neg pos
    else do
        putStrLn $ "Searching at length: " ++ show len
        let funcs = [ (i, filter isPure (generateFuncsAll lang i pos)) | i <- [1..len] ]
        let delta2 = concat $
                        [ [[g1,g2],[g2,g1]]
                                | i <- [1..(len `div` 2)],
                                  g1 <- fromJust (lookup i funcs),
                                  g2 <- fromJust (lookup (len-i) funcs),
                                  --isPure g1,
                                  --isPure g2,
                                  not (numberChange g1),
                                  not (numberChange g2),
                                  if i == (len-i) then g1 /= g2 else True,
                                  not (lhsNotSame g1 g2)
                            ]
        let delta1 =     [ [g]  | g <- fromJust (lookup len funcs),
                                  not (numberChange g)
                                  --isPure g
                          ]
        
        putStrLn $ "    generated functions: " ++ show (length delta1 + length delta2)
        --appendFile "temp.txt"
        --  $ unlines $ map (\x -> concat . intersperse ", " $ map showAxiom x) delta
        
        let func delta = do
                result <- sequence $ parMap rpar (performance width depth sol ltm neg pos ded) delta
                let result' = [(x,y) | (Just x,y) <- result]
                let optimal  = [(x,y) | (x,y) <- result', y == optimum]
                let best = maximum $ map snd result'
                let optimal' = [(x,y) | (x,y) <- result', y == best]
                if (not . null) optimal
                then do    
                    putStrLn $ "Optimal performance: " ++ show optimum
                    putStrLn $ show (length optimal) ++ " optimal deltas found."
                    let delta = chooseBestDelta optimal
                    return $ Just delta
                else do
                    if len == fromIntegral sol && (not . null) optimal'
                    then do putStrLn $ "Best performance: " ++ show optimum
                            putStrLn $ show (length optimal) ++ " best deltas found."
                            let delta = chooseBestDelta optimal'
                            return $ Just delta
                    else return Nothing

        result2 <- func delta2
        if result2 /= Nothing
        then return $ fromJust result2
        else do
            result1 <- func delta1
            if result1 /= Nothing
            then return $ fromJust result1
            else findDelta (len+1) agent neg pos

numberChange (HsLit (HsInt _) :->> _) = True
numberChange (HsLit (HsInt _) :-> _) = True
numberChange _ = False

isPure (p :->> q) = 
    let pvar = nub [HsVar e  |(HsVar e) <- getSubExp p]
        qvar = nub [HsVar e  |(HsVar e) <- getSubExp q]
    in null (qvar \\ pvar)
isPure (p :-> q) = 
    let pvar = nub [HsVar e  |(HsVar e) <- getSubExp p]
        qvar = nub [HsVar e  |(HsVar e) <- getSubExp q]
    in null (qvar \\ pvar)
lhsNotSame ((HsVar _) :->> y) ((HsVar _) :->> q) = True
lhsNotSame ((HsVar _) :->> y) ((HsVar _) :-> q) = True
lhsNotSame ((HsVar _) :-> y) ((HsVar _) :-> q) = True
lhsNotSame ((HsVar _) :-> y) ((HsVar _) :->> q) = True
lhsNotSame (x :->> y) (p :->> q) = x == p
lhsNotSame (x :-> y) (p :-> q) = x == p
lhsNotSame _ _ = False
-----------------------

chooseBestDelta :: [([Axiom],Int)] -> ([Axiom],Int)
chooseBestDelta [] = ([],0)
chooseBestDelta [x] = x
chooseBestDelta deltas =
    let deltas' = [(ax,perf,length [p | p@(_ :->> _) <- ax]) | (ax,perf)  <- deltas]
        maxArrowCount = maximum [arrows | (ax,perf,arrows) <- deltas']
        deltas1 = [(ax,perf) | x@(ax,perf,arrows) <- deltas', arrows == maxArrowCount]
    in if length deltas1 == 1
        then head deltas1
        else let deltas2 = [(ax,perf,sum (map countVars ax)) | (ax,perf)  <- deltas1]
                 maxVarCount = maximum [varCount | (ax,perf,varCount) <- deltas2]
                 deltas3 = [(ax,perf) | x@(ax,perf,vars) <- deltas2, vars == maxVarCount]
             in if length deltas3 == 1
                  then head deltas3
                  else head deltas3

countVars :: Axiom -> Int
countVars (p :->> q) = countVars' p + countVars' q
countVars (p :-> q) = countVars' p + countVars' q
countVars' exp = length [HsVar e  |(HsVar e) <- getSubExp exp]

--learning :: Int -> Word -> Word -> HsModule -> [HsMatch] -> HsMatch -> IO (Maybe HsMatch)
--learning len _ _ _ _ _ | len < 0 = return Nothing
--learning 0 width depth ltm negex m@(HsMatch _ name pats (HsUnGuardedRhs rhs) _) = do
--    let exp = foldl (\exp p -> HsApp exp (patToExp p)) (HsVar (UnQual name)) pats
--    ans <- solveAnswer (fromIntegral width) (fromIntegral depth) ltm (Right exp, [])
--    if ans == (Just rhs)
--      then return Nothing
--      else learning 1 width depth ltm negex m

performance :: Int -> Int -> Int -> [Axiom]
            -> [IP] -> [IP] -> [IP]
            -> Delta -> IO (Maybe Delta,Int)
performance width depth sol ltm negex pos ded func = do
    --putStrLn $ unlines $ map showAxiom func
    let ltm' = ltm ++ func

    ansPos <- mapM (\x@(IP _ _ y) -> do result <- findAnswerDecl ltm' width depth x
                                        return (result,y)) pos
    ansDed <- mapM (\x@(IP _ _ y) -> do result <- findSolDecl ltm' width depth x
                                        return (result,y)) ded
    ansNeg <- mapM (\x@(IP _ _ y) -> do result <- findAnswerDecl ltm' width depth x
                                        return (result,y)) negex
    let posUtil = sum [y | (True,y) <- ansPos]
    let dedUtil = sum [y | (sol,y) <- ansDed,
                           (Right _,_) <- [head sol]]
    let negUtil = sum [y | (True,y) <- ansNeg]
    let util = posUtil + dedUtil - negUtil
    if or (map fst ansNeg)
    then return (Nothing,util)
    else do
        if and (map fst ansPos)
        then do
            if null [x | (x@(Left _),_) <- (map head (map fst ansDed))]
            then return (Just func,util)
            else return (Nothing,util)
        else return (Nothing,util)

generateFuncsAll :: Language -> Int -> [IP] -> Delta
generateFuncsAll _    len _   | len < 2 = []
generateFuncsAll lang len pos =
    let
        parts = [lhs | (IP lhs _ _) <- pos] ++ [rhs | (IP _ rhs _) <- pos]
        units = nub $ [x | x <- (concatMap getSubExp parts), size x == 1]
                      ++ [HsVar (UnQual (HsIdent [c])) | c <- "x"]
                      ++ langUnits lang 1
                      ++ ansatz lang
        unary  = langOps lang 1 ++ [HsVar x | (HsApp (HsVar x) _) <- parts]
        binary = langOps lang 2 ++ [HsVar x | (HsInfixApp _ (HsQVarOp x) _) <- parts]
        
        funcs = [ (i, generateExps i units unary binary) | i <- [1..(len-1)] ]
        result = concat
                 [ [p :->> q, q :->> p]
                      | i <- [1 .. (len `div` 2)],
                        p <- fromJust (lookup i funcs),
                        q <- fromJust (lookup (len - i) funcs),
                        if i == (len-i) then p /= q else True
                  ]
        {-
        pats = nub [p'   |  i <- [1 .. (len-1)],
                                p' <- generateLhs i units lhs,
                                matchExpExp p' lhs]
        exps = [(HsApp (HsVar f) p) :->> exp
                    |  p <- pats,
                       f <- [x | (HsApp (HsVar x) _) <- [lhs]],
                       exp <- generateExps (len - (size p + 1)) units unary binary]
        
        ansatzExps = [p :->> rhs |
                        -- p@(HsApp (HsVar (UnQual f)) ps) <- ansatz lang,
                        p <- ansatz lang,
                        rhs <- generateExps (len - 1) units unary binary]

        exps1 = [p :->> exp
                    |  p <- pats,
                       exp <- generateExps (len - size p) units unary binary,
                       matchExpExp exp rhs]
        exps2 = [p :->> rhs
                    |  p <- pats,
                       size rhs == len - size p]
        result = (exps ++ exps1 ++ exps2 ++ ansatzExps) -- ++ expsexps)
        -}
    in  result -- ++ [x :-> y | (x :->> y) <- result]

-- generate patterns for expressions, given a list of patterns for element types
-- for example,
-- 5 -> _, x, 5
-- 5*3 -> x, 5*x, x*3, 5*3, x*y
-- 1+2 -> x, 1+x, x+2, 1+2, x+y
generateLhs :: Int -> [HsExp] -> HsExp -> [HsExp]
generateLhs len _ _ | len < 1 = []
--generateLhs 1 units e@(HsInfixApp p qn q) -- only to generate (_ * _)
--            = [HsInfixApp x qn y | x <- generateLhs 0 units p,
--                                   y <- generateLhs 0 units q]
--              ++ [u | u <- units, matchExpExp e u]
generateLhs 1 units p         = [u | u <- units]
generateLhs len l (HsNegApp p) = (HsNegApp p) : (map HsNegApp $ generateLhs (len-1) l p)
generateLhs len l (HsParen p) = (HsParen p) : (map HsParen $ generateLhs (len-1) l p)
generateLhs len l (HsInfixApp p1 qn p2)
    = concat $
        [
          [HsInfixApp p1' qn p2'
              |   p1' <- generateLhs i l p1,
                  p2' <- generateLhs (len' - i) l p2]
         | i <- [0 .. len']
        ]
    where len' = len - 1
generateLhs len l (HsApp qn p) = [HsApp qn x | x <- generateLhs (len-1) l p, matchExpExp p x]

generateLhs len xs p@(HsList ps) =
    let pats = generateListPats len []
    in  pats ++ [HsInfixApp x (HsQConOp (Special HsCons)) y
                            | x <- xs,
                              y <- generateListPats (len - 1) (xs \\ [x])]
generateLhs len xs p = []

generateExps :: Int -> [HsExp] -> [HsExp] -> [HsExp] -> [HsExp]
generateExps len _ _ _ | len < 1 = []
generateExps 1 units _ _ = units
generateExps 2 units funcs1 _ = [HsApp x y | x <- funcs1, y <- units]
generateExps len units funcs1 funcs2
    = let exps2 = generateExps (len-2) units funcs1 funcs2
          exps1 = generateExps (len-1) units funcs1 funcs2
      in 
        [HsInfixApp x (HsQVarOp op) y
            | x <- exps2,
              y <- exps2,
              (HsVar op) <- funcs2]
        ++
        [HsApp op arg
              | op <- funcs1,
                arg <- exps1]

{-
generateExps len units funcs1 funcs2 (HsInfixApp x (HsQConOp (Special HsCons)) y)
    = let exps = generateExps (len-1) units funcs1 funcs2 y
          lists = exps ++ [HsList [x]] ++ [HsInfixApp x (HsQConOp (Special HsCons)) l | l <- exps]
      in lists ++ [HsApp f l | l <- lists, f <- funcs1]
         ++ [HsInfixApp l1 (HsQVarOp f) l2
                |   l1 <- lists,
                    l2 <- lists,
                    (HsVar f) <- funcs2,
                    (size l1 + size l2) < len
            ]

generateExps len units funcs1 funcs2 p@(HsInfixApp x qn y)
    = result ++ [HsApp f r | f <- funcs1, r <- result, size r < len]
  where
    result = [HsInfixApp x qn y |
                x <- generateExps (len-2) units funcs1 funcs2 p,
                y <- generateExps (len-2) units funcs1 funcs2 p]
-}

-- generate patterns for list type, given a list of patterns for element types
-- for example, given [1,x], it generates
-- _, xs, [], (x:_), (x:[]), (x:xs), (1:_), (1:[]), (1:xs), (x:1:_), (1:x:_), ...
generateListPats :: Int -> [HsExp] -> [HsExp]
generateListPats len _ | len < 1 = []
generateListPats _   [] = [HsList [],HsVar (UnQual (HsIdent "l"))]
generateListPats len xs =
    let listpats = generateListPats len []
    in  listpats ++ [HsInfixApp x (HsQConOp (Special HsCons)) y
                                | x <- xs,
                                  y <- generateListPats (len - 1) (xs \\ [x])]

-- generate a list of list expressions for each pattern
-- the second argument is a list of functions of type :: [a] -> [a]
-- the third  argument is a list of functions of type :: [a] -> [a] -> [a]
generateListExps :: Int -> [HsExp] -> [HsExp] -> HsExp -> [HsExp]
generateListExps len _ _ _ | len < 1 = [HsList []]
generateListExps _ _ _ HsWildCard = [HsList []]
generateListExps _ _ _ (HsList []) = [HsList []]
generateListExps len funcs1 funcs2 (HsVar x) = [HsVar x] ++ [HsApp f (HsVar x) | f <- funcs1]
generateListExps len funcs1 funcs2 (HsInfixApp x (HsQConOp (Special HsCons)) y)
    = let exps = generateListExps (len-1) funcs1 funcs2 y
          lists = exps ++ [HsList [x]] ++ [HsInfixApp x (HsQConOp (Special HsCons)) l | l <- exps]
      in lists ++ [HsApp f l | l <- lists, f <- funcs1]
         ++ [HsInfixApp l1 (HsQVarOp f) l2 | l1 <- lists, l2 <- lists, (HsVar f) <- funcs2, (size l1 + size l2) < len]
generateListExps _ _ _ _ = [HsList []]


-------------------------------------------------------------------------------
--   HELPER FUNCTIONS
-------------------------------------------------------------------------------

getInt :: Maybe HsExp -> Integer
getInt (Just (HsLit (HsInt i))) = i
getInt _ = 0

getString :: Maybe HsExp -> String
getString (Just (HsLit (HsString s))) = s
getString _ = ""

getModule :: ParseResult HsModule -> HsModule
getModule (ParseOk m) = m

findInfixIndex :: (Eq a) => [a] -> [a] -> Maybe Int
findInfixIndex needle haystack
    = (\x -> if null x then Nothing else Just (fst $ head x))
      . dropWhile (\(_,x) -> not $ isPrefixOf needle x) 
        $ zip [0..] (tails haystack)

getWidth :: [Axiom] -> Int
getWidth axioms = let r = [x | ((HsCon (UnQual (HsIdent "Width"))) :->> HsLit (HsInt x)) <- axioms]
                  in if null r then 0 else (fromIntegral $ head r)

getDepth :: [Axiom] -> Int
getDepth axioms = let r = [x | ((HsCon (UnQual (HsIdent "Depth"))) :->> HsLit (HsInt x)) <- axioms]
                 in if null r then 0 else (fromIntegral $ head r)

getSolution :: [Axiom] -> Int
getSolution axioms = let r = [x | ((HsCon (UnQual (HsIdent "Solution"))) :->> HsLit (HsInt x)) <- axioms]
                  in if null r then 0 else (fromIntegral $ head r)

getFilename :: [Axiom] -> String
getFilename axioms = let r = [x | ((HsCon (UnQual (HsIdent "Filename"))) :->> HsLit (HsString x)) <- axioms]
                  in if null r then "" else (head r)

getLanguage :: [Axiom] -> String
getLanguage axioms = let r = [x | ((HsCon (UnQual (HsIdent "Language"))) :->> HsLit (HsString x)) <- axioms]
                  in if null r then "" else (head r)

-- check if the answer is the same as given, using Astar search
findAnswerDecl :: [Axiom] -> Int -> Int -> IP -> IO Bool
findAnswerDecl ltm width depth (IP exp rhs _) = do
            ans <- solveAnswer (fromIntegral width) (fromIntegral depth) ltm (Right (exp,Nothing), []) (Just rhs)
            return (isJust ans && equalExp (fromJust ans,rhs))
--findAnswerDecl ltm width depth (HsFunBind [HsMatch loc name pats (HsUnGuardedRhs rhs) _]) = do
--            let exp = foldl (\exp p -> HsApp exp (patToExp p)) (HsVar (UnQual name)) pats
--            ans <- solveAnswer (fromIntegral width) (fromIntegral depth) ltm (Right (exp,Nothing), []) (Just rhs)
--            return (isJust ans && equalExp (fromJust ans,rhs))

-- find the solution (all proof steps) using the Astar search
findSolDecl :: [Axiom] -> Int -> Int -> IP -> IO [StateD]
-- if rhs is x, then search for any answer
findSolDecl ltm width depth (IP exp (HsVar (UnQual (HsIdent "x"))) _) = do
        ans <- solve (fromIntegral width) (fromIntegral depth) ltm (Right (exp,Nothing), []) Nothing
        if ans /= Nothing
        then return $ (Right (exp,Nothing), []) : fromJust ans
        else return $ [(Left "No solution found", [])]
-- else search for the given answer
findSolDecl ltm width depth (IP exp rhs _) = do
        ans <- solve (fromIntegral width) (fromIntegral depth) ltm (Right (exp,Nothing), []) (Just rhs)
        if ans /= Nothing
        then return $ (Right (exp,Nothing), []) : fromJust ans
        else return $ [(Left "No solution found", [])]
{-
findSolDecl ltm width depth (HsFunBind [HsMatch loc name pats (HsUnGuardedRhs rhs) _]) = do
            let exp = foldl (\exp p -> HsApp exp (patToExp p)) (HsVar (UnQual name)) pats
            ans <- solve (fromIntegral width) (fromIntegral depth) ltm (Right (exp,Nothing), []) (Just rhs)
            if ans /= Nothing
            then return $ (Right (exp,Nothing), []) : fromJust ans
            else return $ [(Left "No solution found", [])]
findSolDecl ltm width depth (HsFunBind [HsMatch loc name pats (HsUnGuardedRhs (HsVar (UnQual (HsIdent "x")))) _]) = do
            let exp = foldl (\exp p -> HsApp exp (patToExp p)) (HsVar (UnQual name)) pats
            ans <- solve (fromIntegral width) (fromIntegral depth) ltm (Right (exp,Nothing), []) Nothing
            if ans /= Nothing
            then return $ (Right (exp,Nothing), []) : fromJust ans
            else return $ [(Left "No solution found", [])]
-}
-- merge the two HsDecl, one as lhs and one as rhs
mergeHsDecl :: HsDecl -> HsDecl -> (HsExp,HsExp)
mergeHsDecl (HsPatBind _ _ (HsUnGuardedRhs (HsApp (HsVar (UnQual name)) pat)) _) (HsPatBind _ _ (HsUnGuardedRhs exp) _)
    -- = normalDec $ HsFunBind [HsMatch (SrcLoc "" 0 0) name [expToPat pat] (HsUnGuardedRhs exp) []]
    = ((HsApp (HsVar (UnQual name)) pat), exp)
mergeHsDecl (HsPatBind _ _ (HsUnGuardedRhs lhs) _) (HsPatBind _ _ (HsUnGuardedRhs exp) _)
    -- = normalDec $ HsPatBind (SrcLoc "" 0 0) (expToPat lhs) (HsUnGuardedRhs exp) []
    = (lhs, exp)

-------------------------------------------------------------------------------
--   PARSING FUNCTIONS
-------------------------------------------------------------------------------

-- | Parse the training file, return E+ and E- sets
parseTrainingFile :: FilePath -> IO ([IP],[IP])
parseTrainingFile file = do
    text <- readFileSafe file utf8
    let inputs =
              concatMap parseInput
            . map (\(x:xs) -> init xs)
            . filter (\(x:xs) -> x == '(' && (take 1 $ reverse xs) == ")")
            . filter (not . null)
            . map strip
            $ lines text
    putStrLn $ show (length inputs) ++ " axioms read from IP file."
    p <- mapM parseIP $ inputs
    let p' = concat p
    let pos = filter (\x -> val x > 0) p'
    let neg = filter (\x -> val x < 0) p'
    putStrLn $ "pos: "
    putStrLn $ concat $ intersperse "," $ map ("    " ++)
                      $ map prettyIP pos
    putStrLn $ "neg: "
    putStrLn $ concat $ intersperse "," $ map ("    " ++)
                      $ map prettyIP neg
    return $ (pos,neg)

parseIP :: IP' -> IO [IP]
parseIP (a,b,c) = do
    let a' = parseModule $ "main = " ++ a
    let b' = parseModule $ "main = " ++ b
    if not (parseSuccess a') || not (parseSuccess b')
    then return []
    else do
    let a1' = (\(HsModule _ _ _ _ dec) -> dec) $ getModule a'
    let b1' = (\(HsModule _ _ _ _ dec) -> dec) $ getModule b'

    if null a1' || null b1'
    then return []
    else do

    let a1 = head a1'
    let b1 = head b1'
    --putStrLn $ show a1
    --putStrLn $ show b1
    let (p,e) = mergeHsDecl a1 b1
    return [IP (normalExp True p) (normalExp True e) c]

-- parses a line from Agent file, e.g. (3*0,0,1)
parseEq :: String -> IO [Axiom]
parseEp "" = return []
parseEq s = do
    let index1 = findInfixIndex " ->> " s
    
    if index1 == Nothing
    then do
        let index2 = findInfixIndex " -> " s
        if index2 == Nothing
        then return []
        else do
            let a = take (fromJust index2) s
            let b = drop (fromJust index2 + 4) s
            if null a || null b
            then do
            return []
            else do
                let a' = parseModule $ "main = " ++ a
                let b' = parseModule $ "main = " ++ b
                if not (parseSuccess a') || not (parseSuccess b')
                then return []
                else do
                let a1 = (\(HsModule _ _ _ _ dec) -> dec) $ getModule a'
                let b1 = (\(HsModule _ _ _ _ dec) -> dec) $ getModule b'
                let a1' = [e | (HsPatBind _ _ (HsUnGuardedRhs e) _) <- a1]
                let b1' = [e | (HsPatBind _ _ (HsUnGuardedRhs e) _) <- b1]
                return [normalExp False (head a1') :-> normalExp False (head b1')]
    else do
    let a = take (fromJust index1) s
    let b = drop (fromJust index1 + 5) s
    if null a || null b
    then do
        return []
    else do
    let a' = parseModule $ "main = " ++ a
    let b' = parseModule $ "main = " ++ b
    if not (parseSuccess a') || not (parseSuccess b')
    then return []
    else do
    let a1 = (\(HsModule _ _ _ _ dec) -> dec) $ getModule a'
    let b1 = (\(HsModule _ _ _ _ dec) -> dec) $ getModule b'

    let a1' = [e | (HsPatBind _ _ (HsUnGuardedRhs e) _) <- a1]
    let b1' = [e | (HsPatBind _ _ (HsUnGuardedRhs e) _) <- b1]
    return [normalExp False (head a1') :->> normalExp False (head b1')]
    {-
    let a1' = [ e | e@(HsPatBind _ _ (HsUnGuardedRhs (HsApp (HsVar (UnQual n)) p)) _) <- a1]

    let result1 = [HsMatch (SrcLoc "" 0 0) n [expToPat p] (HsUnGuardedRhs rhs) []
                    |   (HsPatBind _ _ (HsUnGuardedRhs (HsApp (HsVar (UnQual n)) p)) _) <- a1',
                        (HsPatBind _ _ (HsUnGuardedRhs rhs) _) <- b1]
    let result2 = [HsPatBind (SrcLoc "" 0 0) (expToPat lhs) (HsUnGuardedRhs rhs) []
                    |   (HsPatBind _ _ (HsUnGuardedRhs lhs) _) <- a1 \\ a1',
                        (HsPatBind _ _ (HsUnGuardedRhs rhs) _) <- b1]
    
    return $ [HsFunBind [normalMatch x] | x <- result1]
              ++ result2
    -}

isHsPatBind (HsPatBind _ _ (HsUnGuardedRhs _) _) = True
isHsPatBind _ = False

parseInput :: String -> [IP']
parseInput "" = []
parseInput s | not (',' `elem` s) = []
parseInput s = if not (null term1) && not (null term2) && (/=0) value
                then [(term1, term2, value)]
                else []
    where
        (a',b') = break (==',') $ reverse s
        b = reverse (if not (null b') then tail b' else b')
        a = reverse a'
        value = if null a
                    then 0
                    else if head a == '-'
                            then if all isDigit (tail a) then (read a :: Int) else 0
                            else if all isDigit a then (read a :: Int) else 0
        (x',y') = if (take 1 $ reverse b) == "]"
                    then let (p,q) = break (=='[') $ reverse b
                         in if null q
                                then ([],[])
                                else (p ++ [head q], tail q)
                    else break (==',') $ reverse b
        term1 = reverse $ if not (null y') then tail y' else y'
        term2 = reverse x'

-- | Read and parse an agent from a file
parseAgent :: FilePath -> IO (Maybe Agent)
parseAgent f = do
        text <- readFileSafe f utf8
        let com = takeWhile (\x -> not (isPrefixOf "-}" (strip x)))
                    $ filter (not . null . strip) $ lines text
        let rest = dropWhile (\x -> not (isPrefixOf "-}" x))
                    $ filter (not . null) $ map strip $ lines text
        if null rest
        then do
            putStrLn $ "Module not found. Failed to parse file " ++ f ++ "."
            return Nothing
        else do

        let (modLine:restLines) = rest
        if null restLines
        then do
            putStrLn $ "Error: Empty agent file " ++ f ++ "."
            putStrLn $ "       Agent file must define width, depth, solution, filename."
            return Nothing
        else do
        axioms' <- mapM parseEq restLines
        let axioms = nub $ concat axioms'
        let width = getWidth axioms
        let depth = getDepth axioms
        let sol   = getSolution axioms
        let file = getFilename axioms
        let lang = getLanguage axioms
        if width == 0 || depth == 0
        then do
            putStrLn $ "Error: Width and depth parameters must be greater than zero."
            return Nothing
        else do
        if file == ""
        then do
            putStrLn $ "Error: filename parameter is not defined."
            putStrLn $ "       It is required for training."
            return Nothing
        else do
        putStrLn $ "Parsed agent "
        putStrLn $ "Width = " ++ show width
        putStrLn $ "Depth = " ++ show depth
        putStrLn $ "Language = " ++ show lang
        putStrLn $ "Traing file = " ++ file
        return $ Just $ Agent (unlines com) (width, depth, sol) lang file axioms
        --return Nothing


parseSuccess :: ParseResult HsModule -> Bool
parseSuccess (ParseOk m) = True
parseSuccess _           = False

-------------------------------------------------------------------------------
--   UNUSED CODE
-------------------------------------------------------------------------------

-- | Generate all functions of the given length
generateFuncs :: HsMatch -> Int -> [HsMatch]
generateFuncs m len | len < 1 = []
generateFuncs (HsMatch loc name pats (HsUnGuardedRhs rhs) x) 1 = [] -- | size rhs == 1
--    = [HsMatch loc name [HsPWildCard] (HsUnGuardedRhs rhs) x]
generateFuncs m@(HsMatch loc name pats (HsUnGuardedRhs rhs) x) 2
    = [HsMatch loc name [HsPVar (HsIdent "x")] (HsUnGuardedRhs (HsVar (UnQual (HsIdent "x")))) x]
        ++ if size m == 2 then [m] else []
generateFuncs m@(HsMatch loc name pats (HsUnGuardedRhs rhs) x) len
        = if size m == len then [m] else []

