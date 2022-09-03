
module Main.Mode.TamiglooMain (
        tamiglooMain
    ,   tamiglooDebug

  ) where

import              Prelude   
-- import              Theory.Text.Pretty
import qualified Text.PrettyPrint.Class          as Pretty
--import              System.FilePath
--import              Theory.Text.Parser.Token(parseFile)
import qualified    Data.Map as Map
import              Main.Console(Arguments, renderDoc)
import              Main.TheoryLoader(loadOpenThy)

import qualified    Theory as T            
import              TamarinToTamigloo
import              TamiglooConfig
-- import qualified    TamiglooDatatypes as TID

-- import              PrettyIOSpecs.PrettyDebug as Debug
import qualified    PrettyIOSpecs.Gobra.Content as Gobra

import qualified    PrettyIOSpecs.VeriFast.Content as VF

import System.Directory (createDirectoryIfMissing)
import System.FilePath



-- stack exec -- tamarin-prover --tamigloo-compiler ../test_examples/test1.spthy


-- wrapper to interface with the batch mode call
tamiglooMain :: Arguments -> FilePath -> IO T.OpenTranslatedTheory
tamiglooMain as fp = do
    config <- tamiglooReadConfig fp
    let inFile = config Map.! "input_file"
    thy <- (loadOpenThy as inFile)
    tamiglooRun config thy
    return thy

-- output that will be printed in command line summary
tamiglooDebug :: T.OpenTranslatedTheory -> Pretty.Doc
tamiglooDebug _thy = (Pretty.emptyDoc)
    -- GobraUtils.printDebug (changeTheory _thy)

-- run a function printing verifier specific tamigloooutput 
-- using the input config (use default options if left unspecified)
tamiglooRun :: Map.Map String String -> T.OpenTranslatedTheory -> IO ()
tamiglooRun config thy = 
    let 
        dflt = defaultConfig config
        tamiThy = changeTheory thy
        v = dflt Map.! "verifier"
    in
        do
            fp <- case () of
                    () | v == "gobra" -> putStrLn("gobra") >> return (Gobra.content dflt tamiThy)
                       | v == "verifast" -> putStrLn("verifast") >> return (VF.content dflt tamiThy)
                       | otherwise -> error "Should not be here. Check default values in TamiglooConfig."
            outGobraDocs fp

-- writes documents to filepaths
outGobraDocs :: [(FilePath, Pretty.Doc)] -> IO ()
outGobraDocs docs = do
    _ <- foldr (uncurry outDoc) (return "") docs
    return ()
-- we use the IO String to force evaluation e.g. in outGobraDocs
-- there is probably a much better way to do this
outDoc :: FilePath -> Pretty.Doc -> IO String -> IO String
outDoc fp doc stringMonad = do
    writeDoc fp (renderDoc doc)
    stringMonad

-- writes a string to a file path. Creates folders if necessary
writeDoc :: FilePath -> String -> IO ()
writeDoc path content = do
  createDirectoryIfMissing False $ takeDirectory path
  writeFile path content



