module PrettyIOSpecs.VeriFast.PermissionEncoding (

          veriFastInternalPermissions
        , veriFastOutPermissions
        , veriFastInPermissions

        , permAppQ



  ) where



--
import              Prelude
-- import qualified    Data.Map as Map
-- import              Data.Maybe(isJust)
-- import              Data.List(elemIndex)
-- import qualified    Data.ByteString.Char8 as BC

-- Tamarin prover imports
import              Text.PrettyPrint.Class
-- import qualified    Theory as T
-- import              Term.LTerm(sortOfLNTerm)
-- Tamigloo imports
-- ---- isabelle generated
import              GenericHelperFunctions(nubBy)
import qualified    TamiglooDatatypes as TID
import qualified    IoSpecs as IOS
-- ---- other Tamigloo modules
import              DerivingInstances
import              PrettyIOSpecs.VeriFast.Utils



{- internal permissions -}
veriFastInternalPermissions :: Document d => TID.Theory -> [(String, d)]
veriFastInternalPermissions thy =
    map roleInternPerms (IOS.extractIOSpec thy)
    where
        roleInternPerms :: Document d => (String, IOSpecWithDefs) -> (String, d)
        roleInternPerms inp =
            let 
                role = fst inp
                formulas = map snd $ IOS.getAbsPhisWithDef (snd inp)
                perms = permEncoding formulas TID.Internal_R
            in
                (role, ghostBlock $ vcat perms)


veriFastOutPermissions :: Document d => TID.Theory -> d
veriFastOutPermissions thy = veriFastPermissions thy TID.Out_RG

veriFastInPermissions :: Document d => TID.Theory -> d
veriFastInPermissions thy = veriFastPermissions thy TID.In_RF

veriFastPermissions :: Document d => TID.Theory -> TID.PermType -> d
veriFastPermissions thy permType =
    let
        formulas = -- all defs regardless of role
            concatMap (\inp -> map snd $ IOS.getAbsPhisWithDef (snd inp)) (IOS.extractIOSpec thy)
    in
        ghostBlock $
            vcat $ permEncoding formulas permType


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
singlePerm p@(TID.IOSFpred (TID.Perm permType _name) _) =
    let
        def = 
            (permDef p) -- perm
    in
        (case permType of
            TID.Out_RG -> def
            TID.Internal_R -> def <> text "\n" $$ (internBIO p)
            TID.In_RF -> def) <>
        text "\n\n"
singlePerm _ = error "singlePerm called with wrong arguments."

-- definition of a permission (permission encoding)
permDef :: Document d => TID.IOSFormula -> d
permDef (TID.IOSFpred (TID.Perm _ name) ts) =
    let
        termsWithType = map (\t -> text (printTypeOfIOSTerm t) <> text " " <> (prettyVFIOSTerm False) t) ts
    in
        text "predicate " <> functionAppDoc (text name) termsWithType <> text ";"
permDef _ = error "permDef called with wrong arguments."

permAppQ :: Document d => TID.IOSFormula -> d
permAppQ (TID.IOSFpred (TID.Perm permType name) ts) =
    let
        pOp = (TID.Perm permType name)
        termDocs = map (prettyVFIOSTerm False) ts

        args = listPermArgTerms pOp termDocs
        rets = listPermReturnTerms pOp termDocs
        retsQ = map (\r -> text "?" <> r) rets
    in
        functionAppDoc (text name) (args ++ retsQ)
permAppQ _ = error "permAppQ called with wrong arguments."

-- definition of an internal basic input output operation
internBIO :: Document d => TID.IOSFormula -> d
internBIO p@(TID.IOSFpred (TID.Perm TID.Internal_R name) ts) =
    let
        pOp = (TID.Perm TID.Internal_R name)
        termDocs = map (prettyVFIOSTerm False) ts

        permApp = permAppQ p

        placeSrc = head termDocs
        placeDst = last termDocs

        termsWithType = map (\t -> text (printTypeOfIOSTerm t) <> text " " <> (prettyVFIOSTerm False) t) ts
        argsWithType = listPermArgTerms pOp termsWithType
    in
        lemma 
            (text "void") 
            (text $ "internBIO_" ++ name) 
            argsWithType 
            (text "token(" <> placeSrc <> text ") &*& " <> permApp)
            (text "token(" <> placeDst <> text ")")
            (text "assume(false);")
internBIO _ = error "internBIO called with wrong arguments."