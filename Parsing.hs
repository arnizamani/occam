-------------------------------------------------------------------------------
--   PARSING FUNCTIONS
-------------------------------------------------------------------------------

module Parsing where
import Instances
import Haskell
import Language.Haskell.Syntax
import Language.Haskell.Parser
import Data.List
import Data.Word
import Data.Char
import Data.Maybe
import System.IO
import Niz

type Language = String
type Width = Int
type Depth = Int
type Solution = Int
type Comments = String
-- data Language = Boolean | List | Math | Logic | Stream | Analogy2 | Clause
--     deriving (Eq, Show)
data Agent = Agent Comments (Width, Depth, Solution) Language FilePath [Axiom]
data IP  = IP {lhs :: Lhs, rhs :: Rhs, val :: Int}
type IP' = (String,String,Int)

instance Size IP where
    size (IP x y _) = size x + size y

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

-- merge the two HsDecl, one as lhs and one as rhs
mergeHsDecl :: HsDecl -> HsDecl -> (HsExp,HsExp)
mergeHsDecl (HsPatBind _ _ (HsUnGuardedRhs (HsApp (HsVar (UnQual name)) pat)) _) (HsPatBind _ _ (HsUnGuardedRhs exp) _)
    -- = normalDec $ HsFunBind [HsMatch (SrcLoc "" 0 0) name [expToPat pat] (HsUnGuardedRhs exp) []]
    = ((HsApp (HsVar (UnQual name)) pat), exp)
mergeHsDecl (HsPatBind _ _ (HsUnGuardedRhs lhs) _) (HsPatBind _ _ (HsUnGuardedRhs exp) _)
    -- = normalDec $ HsPatBind (SrcLoc "" 0 0) (expToPat lhs) (HsUnGuardedRhs exp) []
    = (lhs, exp)

getModule :: ParseResult HsModule -> HsModule
getModule (ParseOk m) = m

findInfixIndex :: (Eq a) => [a] -> [a] -> Maybe Int
findInfixIndex needle haystack
    = (\x -> if null x then Nothing else Just (fst $ head x))
      . dropWhile (\(_,x) -> not $ isPrefixOf needle x) 
        $ zip [0..] (tails haystack)

prettyIP :: IP -> String
prettyIP (IP p e v) = showExp p ++ " = " ++ showExp e ++ ": " ++ show v

