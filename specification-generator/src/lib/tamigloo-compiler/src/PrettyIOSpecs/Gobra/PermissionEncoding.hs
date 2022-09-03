module PrettyIOSpecs.Gobra.PermissionEncoding (

          gobraInternalPermissions
        , gobraOutPermissions
        , gobraInPermissions

        , permApp

        , replacePermRetValues
        , getPermToLNTerm

        , mappingRetTermsGetterTerms



  ) where



--
import              Prelude
import qualified    Data.Map as Map
import              Data.Maybe(isJust)
import              Data.List(elemIndex)
import qualified    Data.ByteString.Char8 as BC

-- Tamarin prover imports
import              Text.PrettyPrint.Class
import qualified    Theory as T
import              Term.LTerm(sortOfLNTerm)
-- Tamigloo imports
-- ---- isabelle generated
import              GenericHelperFunctions(nubBy)
import qualified    TamiglooDatatypes as TID
import qualified    IoSpecs as IOS
-- ---- other Tamigloo modules
import              DerivingInstances
import              PrettyIOSpecs.Gobra.Utils




-- TODO comments in encodings to better show which permissions belong to which rules

gobraInternalPermissions :: Document d => Map.Map String String -> TID.Theory -> [(String, d)]
gobraInternalPermissions config thy =
    map (\p -> (fst p, header $ snd p)) (internPerms thy)
    where
        header :: Document d => d -> d
        header body =
            gobraHeader config "iospec"
                ["claim", "fact", "term", "place", "pub", "fresh"]
                body

{- internal permissions -}
internPerms :: Document d => TID.Theory -> [(String, d)]
internPerms thy =
    map roleInternPerms (IOS.extractIOSpec thy)
    where
        roleInternPerms :: Document d => (String, IOSpecWithDefs) -> (String, d)
        roleInternPerms inp =
            let 
                role = fst inp
                formulas = map snd $ IOS.getAbsPhisWithDef (snd inp)
                perms = permEncoding formulas TID.Internal_R
            in
                (role, vcat perms)

gobraOutPermissions :: Document d => Map.Map String String -> TID.Theory -> d
gobraOutPermissions config thy =
    let
        formulas = -- all defs regardless of role
            concatMap (\inp -> map snd $ IOS.getAbsPhisWithDef (snd inp)) (IOS.extractIOSpec thy)
    in
        gobraHeader config "iospec"
            ["claim", "fact", "term", "place", "pub", "fresh"]
        (
            vcat $ permEncoding formulas TID.Out_RG
        )

gobraInPermissions :: Document d => Map.Map String String -> TID.Theory -> d
gobraInPermissions config thy =
    let
        formulas = -- all defs regardless of role
            concatMap (\inp -> map snd $ IOS.getAbsPhisWithDef (snd inp)) (IOS.extractIOSpec thy)
    in
        gobraHeader config "iospec"
            ["claim", "fact", "term", "place", "pub", "fresh"]
        (
            vcat $ permEncoding formulas TID.In_RF
        )

-- encoding of all permissions of a given PermType in a list of IOSFormulas
permEncoding :: Document d => [TID.IOSFormula] -> TID.PermType -> [d]
permEncoding formulas permType = 
    let 
        permPreds = 
            nubBy (\a b -> TID.accPredOpId a == TID.accPredOpId b) $ 
                TID.filterIOSFpredsFromFormulas 
                    (TID.isPermType permType . TID.accPredOpId) 
                    formulas
    in
        map singlePerm permPreds

-- encoding of a single permission
singlePerm :: Document d => TID.IOSFormula -> d
singlePerm p@(TID.IOSFpred (TID.Perm permType name) _) =
    let
        def = 
            (permDef p) <> (text "\n") $$ -- perm
            (vcat $ punctuate (text "\n") $ getPermDef p)  -- getter p dst
    in
        text ("// permission " ++ name) $$ --  " corresponds to rule " ++ ruleName ++ "\n" ++
        (case permType of
            TID.Out_RG -> def
            TID.Internal_R -> def <> text "\n" $$ (internBIO p)
            TID.In_RF -> def) <>
        text "\n\n"



-- application of a permission
permApp :: Document d => TID.IOSFormula -> d
permApp p@(TID.IOSFpred (TID.Perm _ name) ts) =
    let
        terms = (map (prettyGobraIOSTerm False)  $ permArgTerms p)
    in
        functionAppDoc (text name) terms

-- definition of a permission (permission encoding)
permDef :: Document d => TID.IOSFormula -> d
permDef p@(TID.IOSFpred (TID.Perm _ name) ts) =
    let
        argTerms = permArgTerms p
        types = map (text . printTypeOfIOSTerm) argTerms
        termNames = map (prettyGobraIOSTerm False) argTerms
        -- termNames = ["placeSrc", "rid"] ++ (convenienceNames (length argTerms - 2) "a")
        termsWithType = zipWith (\a b -> text "ghost " <> a <> text " " <> b) termNames types
    in
        text "pred " <> functionAppDoc (text name) termsWithType

-- definition of the getter functions of a permission
getPermDef :: Document d => TID.IOSFormula -> [d]
getPermDef p@(TID.IOSFpred (TID.Perm _ name) ts) =
    map
        (uncurry
            (\nr nrt -> 
                functionDefPerm 
                    p 
                    (permGetterName p nr)
                    (map prettyGobraIOSTermWithType $ permArgTerms p)
                    ("(" ++ nrt ++ ")"))
        )
        (zip (nameRetTerms p) (nameRetTermsWithType p))
    where
        functionDefPerm :: Document d => TID.IOSFormula -> String -> [d] -> String -> d
        functionDefPerm p@(TID.IOSFpred (TID.Perm _ _) _) name termsWithType retTermWithType =
            text "ghost" $$
            text "requires " <> permApp p $$
            text "pure " <> functionDefDoc (text name) termsWithType (text retTermWithType)

-- the names of the return values of a permission as named as r1, ..., rn, placeDst
nameRetTerms :: TID.IOSFormula -> [String]
nameRetTerms p@(TID.IOSFpred (TID.Perm _ _) _) =
    (convenienceNames (length (permReturnTerms p) - 1) "r") ++ ["placeDst"]

-- names and types of the return values e.g. r1 Term, ..., rn Fresh, placeDst Place
nameRetTermsWithType :: TID.IOSFormula -> [String]
nameRetTermsWithType p@(TID.IOSFpred (TID.Perm _ _) ts) =
    zipWith (\a b -> a ++ " " ++ b) (nameRetTerms p) (map printTypeOfIOSTerm $ permReturnTerms p)

-- give a name to a getter function of a permission
permGetterName :: TID.IOSFormula -> String -> String
permGetterName p@(TID.IOSFpred (TID.Perm _ name) _) suffix =
    "get_" ++ name ++ "_" ++ suffix 

-- applications of the getters of a permission
getPermApp :: Document d => TID.IOSFormula -> [d]
getPermApp p@(TID.IOSFpred (TID.Perm _ _) ts) =
    map
        (\nr -> functionAppDoc (text $ permGetterName p nr) (map (prettyGobraIOSTerm False) $ permArgTerms p))
        (nameRetTerms p)

-- application of a permission
singleGetPermApp :: Document d => TID.IOSFormula -> Int -> d
singleGetPermApp p@(TID.IOSFpred (TID.Perm _ _) ts) idx =
    let
        nr = (nameRetTerms p) !! idx 
    in
        functionAppDoc (text $ permGetterName p nr) (map (prettyGobraIOSTerm False) $ permArgTerms p)

getPermToLNTerm :: TID.IOSFormula -> [T.LNTerm]
getPermToLNTerm p@(TID.IOSFpred (TID.Perm _ _) ts) =
    map
        (\suffix -> 
            T.FAPP 
                (getPermFunSym (permGetterName p suffix) p) 
                (map TID.getLNTermFromIOSTerm $ permArgTerms p)
        )
        (nameRetTerms p)

getPermFunSym :: String -> TID.IOSFormula -> T.FunSym
getPermFunSym name p@(TID.IOSFpred (TID.Perm _ _) ts) =
    T.NoEq ( BC.pack name, (length (permArgTerms p), T.Public))

singleGetPermToLNTerm :: TID.IOSFormula -> Int -> T.LNTerm
singleGetPermToLNTerm p idx = getPermToLNTerm p !! idx


replacePermRetValues :: TID.IOSFormula -> TID.IOSFormula -> TID.IOSFormula
replacePermRetValues p@(TID.IOSFpred (TID.Perm _ _) ts) f =
    TID.mapTermsInFormula (\_ -> replacePermRetIOSTerm p) f

replacePermRetIOSTerm :: TID.IOSFormula -> TID.IOSTerm -> TID.IOSTerm
replacePermRetIOSTerm perm term =
    case term of
        TID.IOSTermVar lnTerm -> TID.IOSTermVar (replacePermRetLNTerm perm lnTerm)
        TID.IOSTermFacts facts -> TID.IOSTermFacts (mapFactsPerm facts)
        TID.IOSTermClaims facts -> TID.IOSTermClaims (mapFactsPerm facts)
        TID.IOSTermSetOp pOp iosTerms -> TID.IOSTermSetOp pOp (map (replacePermRetIOSTerm perm) iosTerms)
    where
        mapFactsPerm :: [TID.Fact] -> [TID.Fact]
        mapFactsPerm fs = map (mapFact (replacePermRetLNTerm perm)) fs
        mapFact :: (T.LNTerm -> T.LNTerm) -> TID.Fact -> TID.Fact
        mapFact f (TID.Fact fg ft lnTerms) = TID.Fact fg ft (map f lnTerms) 

replacePermRetLNTerm :: TID.IOSFormula -> T.LNTerm -> T.LNTerm
replacePermRetLNTerm p@(TID.IOSFpred (TID.Perm _ _) ts) term =
    let
        maybeIdx = elemIndex term (map TID.getLNTermFromIOSTerm $ permReturnTerms p)
        idx = maybe 0 id maybeIdx
    in
        if isJust maybeIdx -- term is returned by permission (getter exists)
        then
            singleGetPermToLNTerm p idx
        else
            term

mappingRetTermsGetterTerms :: TID.IOSFormula -> Map.Map T.LNTerm T.LNTerm
mappingRetTermsGetterTerms perm =
    let
        returnLNTerms = (map TID.getLNTermFromIOSTerm $ permReturnTerms perm)
        getters = getPermToLNTerm perm
    in
        Map.fromList (zip getters returnLNTerms)




-- definition of an internal basic input output operation
internBIO :: Document d => TID.IOSFormula -> d
internBIO p@(TID.IOSFpred (TID.Perm TID.Internal_R name) ts) =
    let
        pOp = (TID.Perm TID.Internal_R name)
        placeSrc = prettyGobraIOSTerm False $ head ts
        placeDst = prettyGobraIOSTerm False $ last ts
        termsWithType = (map prettyGobraIOSTermWithType ts)

        argsWithType = listPermArgTerms pOp termsWithType
        retTermWithType = head (listPermReturnTerms pOp termsWithType)
    in
        text "ghost" $$
        text "requires token(" <> placeSrc <> text ") && " <> permApp p $$
        text "ensures token(" <> placeDst <> text ") && " <> placeDst <> text " == old(" <>
        (getPermApp p !! 0) <> text ")" $$ 
        functionDefDoc (text $ "internBIO_" ++ name) argsWithType (parens retTermWithType) 


