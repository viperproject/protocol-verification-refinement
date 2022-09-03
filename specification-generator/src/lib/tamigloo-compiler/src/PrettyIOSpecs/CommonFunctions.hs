module PrettyIOSpecs.CommonFunctions (

            makeNameConst
        ,   printTypeOfLSort
        ,   prettyFacts
        ,   prettyFactGeneric
        ,   convenienceNames
        ,   expectsBin

        ,   permReturnTerms
        ,   listPermReturnTerms
        ,   permArgTerms
        ,   listPermArgTerms

        ,   functionAppDocMLine
        ,   functionAppDoc
        ,   functionDefDoc
        ,   functionApp
        ,   functionDef
        ,   joinString
      --  ,   enum
        ,   sepTerms
        ,   bracesInline

  ) where

--
import Prelude
-- Tamarin prover imports
import              Text.PrettyPrint.Class
import qualified    Theory as T

-- Tamigloo imports
-- ---- isabelle generated
import qualified    TamiglooDatatypes as TID
-- ---- other Tamigloo modules
import DerivingInstances()

--Naming
makeNameConst :: T.Name -> String
makeNameConst (T.Name nTag name) = "const_" ++
    case nTag of
        T.FreshName -> show name ++ "_fr"
        T.PubName -> show name ++ "_pub"
        T.NodeName -> show name ++ "_node"

printTypeOfLSort :: T.LSort -> String
printTypeOfLSort ls = case ls of
    T.LSortPub -> "Pub"
    T.LSortFresh -> "Fresh"
    T.LSortMsg -> "Term"
    T.LSortNode -> error "Should not be here"

prettyFacts :: Document d => (TID.Fact -> String) -> [TID.Fact] -> d
prettyFacts prFact fs = vcat $ punctuate (text ",") (map (text . prFact) fs)

prettyFactGeneric :: (T.LNTerm -> String) -> TID.Fact -> String
prettyFactGeneric prTerm (TID.Fact _ ft fts) =
        functionApp (TID.getNameFactTag ft) (map prTerm fts)

convenienceNames :: Int -> String -> [String]
convenienceNames len prefix = (zipWith (++) (repeat prefix) (map show [1..len]))

expectsBin :: [a] -> b -> b
expectsBin ts b =
    if length ts /= 2
    then error $ "Error expected binary: wrong number of args! Num args: "++(show $ length ts)
    else b

-- Permissions

-- gives the return values (input values) of a permission
permReturnTerms :: TID.IOSFormula -> [TID.IOSTerm]
permReturnTerms (TID.IOSFpred pOp ts) = listPermReturnTerms pOp ts

listPermReturnTerms :: TID.PredOpId -> [a] -> [a]
listPermReturnTerms (TID.Perm TID.In_RF _) ts = tail (tail ts) -- everything except src place and rid
listPermReturnTerms (TID.Perm _ _) ts = [last ts] -- target place

-- gives the arguments (output values) of a permission
permArgTerms :: TID.IOSFormula -> [TID.IOSTerm]
permArgTerms (TID.IOSFpred pOp ts) = listPermArgTerms pOp ts

listPermArgTerms :: TID.PredOpId -> [a] -> [a]
listPermArgTerms (TID.Perm TID.In_RF _) ts = take 2 ts
listPermArgTerms (TID.Perm _ _) ts = init ts



-- Formatting
functionAppDocMLine :: Document d => d -> [d] -> d
functionAppDocMLine name args = name <> text "(" $$ nest 4 (vsepTerms args) $$ text ")"

functionAppDoc :: Document d => d -> [d] -> d
functionAppDoc name args = name <> text "(" <> sepTerms args <> text ")"

functionDefDoc :: Document d => d -> [d] -> d -> d
functionDefDoc name args ret = text "func " <> (functionAppDoc name args) <> text " " <> ret

functionApp :: String -> [String] -> String
functionApp name args = (name ++ "(" ++ (joinString ", " args) ++ ")")

functionDef :: String -> [String] -> String -> String
functionDef name args ret = "func " ++ (functionApp name args) ++ " " ++ ret

joinString :: String -> [String] -> String
joinString delimiter args =
    case args of
        [] -> ""
        [a] -> a
        (a:b:as) -> a ++ delimiter ++ joinString delimiter (b:as) 

{-
enum :: [a] -> [(a,Integer)]
enum ls = zip ls [0..]
-}
sepTerms :: Document d => [d] -> d
sepTerms ds =  (hcat $ punctuate (text ", ") ds)

vsepTerms :: Document d => [d] -> d
vsepTerms ds = (vcat $ punctuate (text ", ") ds)

bracesInline :: Document d => d -> d
bracesInline body = text "{ " <> body <> text " }"