module PrettyIOSpecs.Gobra.Content (

    
        content


  ) where

import              Prelude
import qualified    Data.Map as Map
import              Text.PrettyPrint.Class
import System.FilePath

import qualified    Theory as T
import qualified    Theory.Model.Formula as Form

import              TamiglooConfig
import qualified    TamiglooDatatypes as TID
import qualified    IoSpecs as IOS
-- import              Arith (integer_of_nat)

import PrettyIOSpecs.Gobra.Utils
import PrettyIOSpecs.Gobra.TermEncoding
import PrettyIOSpecs.Gobra.FactEncoding
import PrettyIOSpecs.Gobra.PermissionEncoding
import PrettyIOSpecs.Gobra.IOSpecs
import PrettyIOSpecs.Gobra.BytesEncoding




content :: Document d => Map.Map String String -> TID.Theory -> [(String, d)]
content config tamiThy =
    if read (config Map.! "make_go_mod") 
    then (generatePathsWithContent config tamiThy)
    else tail (generatePathsWithContent config tamiThy)

generatePathsWithContent :: Document d => Map.Map String String -> TID.Theory -> [(String, d)]
generatePathsWithContent config tamiThy =
    goMod ++
    readMe ++
    debug ++
    encodings ++
    permissions ++
    iospecs
    where
        encodings :: Document d => [(String, d)]
        encodings =
            (map (\p -> (config Map.! (fst p), snd p)) $
            [ ("path_claim", gobraClaimEncoding config tamiThy)
            , ("path_fact", gobraFactEncoding config tamiThy)
            , ("path_term", gobraTermEncoding config tamiThy)
            , ("path_place", gobraPlaceEncoding config)
            , ("path_pub", gobraPubEncoding config tamiThy)
            , ("path_fresh", gobraFreshEncoding config)
            ]) ++
            [(config Map.! "base_dir" </> "bytes/bytes.gobra", gobraBytesEncoding config tamiThy)]
        permissions :: Document d => [(String, d)]
        permissions =
            let
                base = takeDirectory (config Map.! "path_iospec")
                permsIntern = gobraInternalPermissions config tamiThy
                pathsIntern = map (\p -> base </> "permissions_" ++ (fst p) ++ "_internal.gobra") permsIntern
                permsOut = gobraOutPermissions config tamiThy
                pathOut = base </> "permissions_out.gobra"
                permsIn = gobraInPermissions config tamiThy
                pathIn = base </> "permissions_in.gobra"
            in
                (pathOut, permsOut) : 
                (pathIn, permsIn) : 
                (zip pathsIntern (map snd permsIntern))
        iospecs :: Document d => [(String, d)]
        iospecs =
            let
                base = takeDirectory (config Map.! "path_iospec")
                iospecs = gobraIOSpecs config tamiThy
                paths = map (\p -> base </> (fst p) ++ ".gobra") iospecs
            in
                (zip paths (map snd iospecs))
        debug :: Document d => [(String, d)]
        debug =
            [(config Map.! "base_dir" </> "tamiglooModel.debug", 
                printDebug tamiThy $$ prettyGobraRestrs tamiThy)]
        readMe :: Document d => [(String, d)]
        readMe = [(config Map.! "base_dir" </> "readMe.txt", readMeFile config permissions iospecs)]
        goMod :: Document d => [(String, d)]
        goMod =
            [(config Map.! "base_dir" </> "go.mod", text ("module " ++ (config Map.! "module")))]

-- creates the content of a readme file (how to use I/O specifications with a verifier)
readMeFile :: Document d => Map.Map String String -> [(String, d)] -> [(String, d)] -> d
readMeFile config perms ios =
    let
        relPaths = Map.elems $ defaultRelativePaths
    in
        text "Running the following commands from the base directory (directory where the readme resides) will verify the respective generated encoding using the provided Gobra jar." $$
        text "\n" $$
        (vcat $ map auxReadMe relPaths)

    where
        auxReadMe :: Document d => FilePath -> d 
        auxReadMe inputRelPath =
            if (takeDirectory inputRelPath) == "iospec"
            then vcat $ map (readMeLine config <>) readMeIOS
            else readMeLine config <> text inputRelPath
        -- I/O specifications are dependent on permission files
        readMeIOS :: Document d => [d]
        readMeIOS =
            let
                permsSuffix = map (text . ((</>) "iospec") . takeFileName . fst) perms
                permsInOut = ("iospec" </> "permissions_in.gobra") ++ " " ++ ("iospec" </> "permissions_out.gobra")
                iosDepends =
                    (\p ->
                        let 
                            r = (takeFileName $ dropExtension $ fst p)
                        in 
                           permsInOut ++ " " ++
                           ("iospec" </> ("permissions_" ++ r ++ "_internal.gobra")) ++ " " ++
                           ("iospec" </> takeFileName (fst p))
                    )
                iosSuffix = map (text . iosDepends) ios
            in
                permsSuffix ++ iosSuffix

-- returns the command to run the gobra verifier on a file from the base directory
readMeLine :: Document d => Map.Map String String -> d
readMeLine config = 
        text "java -Xss128m -jar "
    <>  text (config Map.! "gobra_jar")
    <>  text " -I ./ "
    <>  text "--module " 
    <>  text (config Map.! "module")
    <>  text " -i "

