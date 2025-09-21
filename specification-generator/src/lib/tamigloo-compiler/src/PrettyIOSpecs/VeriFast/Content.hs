module PrettyIOSpecs.VeriFast.Content (

    
        content


  ) where

import              Prelude
import qualified    Data.Map as Map
import              Text.PrettyPrint.Class
import              System.FilePath
-- import              Text.RawString.QQ

-- import qualified    Theory as T
-- import qualified    Theory.Model.Formula as Form

-- import              TamiglooConfig
import qualified    TamiglooDatatypes as TID
-- import qualified    IoSpecs as IOS
import              GenericHelperFunctions(nub)
-- import              Arith (integer_of_nat)

-- import PrettyIOSpecs.VeriFast.Utils
import PrettyIOSpecs.VeriFast.TermEncoding
import PrettyIOSpecs.VeriFast.FactEncoding
import PrettyIOSpecs.VeriFast.PermissionEncoding
import PrettyIOSpecs.VeriFast.IOSpecs
import PrettyIOSpecs.VeriFast.BytesEncoding

content:: Document d => Map.Map String String -> TID.Theory -> [(FilePath, d)]
content = generatePathsWithContent

generatePathsWithContent :: Document d => Map.Map String String -> TID.Theory -> [(FilePath, d)]
generatePathsWithContent config tamiThy =
    main ++
    encodings ++
    permissions ++
    iospecs
    where
        encodings = concat
            [ dirPath config "fresh" "fresh" [] veriFastFreshEncoding
            , dirPath config "pub" "pub" [] (veriFastPubEncoding tamiThy)
            , dirPath config "term" "term" ["fresh", "pub"] (veriFastTermEncoding tamiThy)
            , dirPath config "fact" "fact" ["fresh", "pub", "term"] (veriFastFactEncoding tamiThy) -- maybe add multiset encoding here
            , dirPath config "claim" "claim" ["fresh", "pub", "term"] (veriFastClaimEncoding tamiThy)
            , dirPath config "place" "place" [] (veriFastPlaceEncoding)
            , dirPath config "bytes" "bytes" ["pub", "term"] (veriFastBytesEncoding tamiThy)
            ]
        permissions = concat $
            [ dirPath config "iospec" "permissions_out" ["place", "fresh", "pub", "term"] (veriFastOutPermissions tamiThy)
            , dirPath config "iospec" "permissions_in" ["place", "fresh", "pub", "term"] (veriFastInPermissions tamiThy)
            ]
            ++
            (map
                (\p ->
                    dirPath config "iospec" 
                    ("permissions_" ++ fst p)
                    ["place", "fresh", "pub", "term", "fact", "claim"] (snd p))
                (veriFastInternalPermissions tamiThy)
            )
        iospecs = concat $
            map
                (\p ->
                    dirPath config "iospec" 
                    (fst p)
                    ["place", "fresh", "pub", "term", "fact", "claim", "permissions_in", "permissions_out", "permissions_" ++ fst p] (snd p))
                (veriFastIOSpecs tamiThy)
        main =
            let
                jarsrcContent = vcat $ map text $ nub $
                    map -- get relative paths
                        (\p -> takeFileName $ (replaceExtension (fst p) ".jar"))
                        (encodings ++ permissions ++ iospecs)
            in
                [(config Map.! "base_dir" </> "main.jarsrc", jarsrcContent)]


dirPath :: Document d => Map.Map String String -> String -> String -> [String] -> d -> [(FilePath, d)]
dirPath config packageName fileName dependencies body =
    let
        localDir = config Map.! "base_dir"
        jarspecPath = localDir </> (fileName ++ ".jarspec")
        jarspecContent = vcat (map (\n -> text $ n ++ ".jarspec") dependencies) $$ text (fileName ++ ".javaspec")
        javaspecPath = localDir </> (fileName ++ ".javaspec")
        javaspecContent =
                text ("package " ++ packageName ++ ";\n") $$
                vcat (map (\dep -> text ("import " ++ dep ++ ".*;")) dependencies) $$ text "\n\n" $$
                body
    in
    [ (jarspecPath, jarspecContent)
    , (javaspecPath, javaspecContent)
    ]

{-
dropPrefix :: Eq a => [a] -> [a] -> [a]
dropPrefix [] l = l
dropPrefix _ [] = error "Prefix is longer than list."
dropPrefix (p:ps) (x:xs) = if p == x then dropPrefix ps xs else error "Not a prefix."
-}  


