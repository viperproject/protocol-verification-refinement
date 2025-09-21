module TamiglooConfig(


        defaultConfig
    ,   tamiglooReadConfig



) where

import              Prelude
import qualified    Data.Map as Map
-- import              System.FilePath

-- Takes the inputConfig from user and fills up unspecified options with the defaults
-- Also calculates the paths for import statements, etc and adds them to config
-- A minimal working input config needs to contain the base_dir and input_file key
defaultConfig :: Map.Map String String -> Map.Map String String
defaultConfig inputConfig =
    -- Map.union is left-biased: in case of duplicates left value is kept
    -- add default options if not specified
    Map.union inputConfig defaultOptions

-- supported options
defaultOptions :: Map.Map String String
defaultOptions =
    Map.fromList(
        [ ("triggers", "Lhs")
        , ("module", "")
        , ("gobra_jar", "")
        , ("input_file", "")
        , ("make_go_mod", "False") 
        , ("verifier", "gobra")
        -- ("base_dir", "needs to be specified")
        ])

-- reads a file (containing an even number of whitespace separated words)
-- and turns it into a String key-value Map
tamiglooReadConfig :: FilePath -> IO (Map.Map String String)
tamiglooReadConfig inFile = do
    inp <- readFile inFile
    return (readConfig inp)

-- Takes a String of an even number of whitespace separated words
-- and turns them into a String key-value Map
readConfig :: String -> Map.Map String String
readConfig s = 
    let
        ws = words s
    in
        if odd (length ws)
        then error "odd number of config words"
        else Map.fromList (makePairs ws)
    where
        makePairs :: [a] -> [(a,a)]
        makePairs [] = []
        makePairs (a:b:cs) = (a, b) : (makePairs cs)
        makePairs [_] = error "Should not be here: makePairs singleton list"


