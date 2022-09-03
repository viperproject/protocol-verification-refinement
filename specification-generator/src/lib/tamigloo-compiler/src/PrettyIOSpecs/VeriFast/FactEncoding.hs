module PrettyIOSpecs.VeriFast.FactEncoding (

          veriFastFactEncoding
        , veriFastClaimEncoding

  ) where

--
import              Prelude
-- import qualified    Data.Map as Map

-- Tamarin prover imports
import              Text.PrettyPrint.Class

-- Tamigloo imports
-- ---- isabelle generated
import              GenericHelperFunctions(nubBy)
import qualified    TamiglooDatatypes as TID
import qualified    IoSpecs as IOS
-- ---- other Tamigloo modules
import              PrettyIOSpecs.VeriFast.Utils
import              PrettyIOSpecs.VeriFast.MultiSetEncoding




veriFastFactEncoding :: Document d => TID.Theory -> d
veriFastFactEncoding thy =
    factDef thy $$
    hardcodedFunctions

hardcodedFunctions :: Document d => d
hardcodedFunctions =
    ghostBlock $
        hardcodedMsetEncoding $$
        filterIsLinFunc $$
        filterIsPersFunc $$
        mFunc $$
        uFunc




factDef :: Document d => TID.Theory -> d
factDef tamiThy =
    let 
        facts = (collectFactsIOSFormulas . getDefsFromIOSpecs $ tamiThy)
        factConstructors = map factConstr facts
    in
    ghostBlock $
        text "inductive Fact =" $$
        nest 8 (text (head factConstructors)) $$
        nest 4 (vcat $ map (text . ((++) "|   ")) (tail factConstructors)) <> text ";" $$
        text "\n\n" $$
        persistentFunc facts $$
        linearFunc
    where
        collectFactsIOSFormulas :: [TID.IOSFormula] -> [TID.Fact]
        collectFactsIOSFormulas fs = nubBy TID.eqFactSig $ concat $ map (TID.getFactsFromFormula TID.getFactsFromIOSTerm) fs
        getDefsFromIOSpecs :: TID.Theory -> [TID.IOSFormula]
        getDefsFromIOSpecs thy = 
            concat $ map ((map snd) . IOS.getAbsPhisWithDef . snd) (IOS.extractIOSpec thy)

factConstr :: TID.Fact -> String
factConstr (TID.Fact _ ft fts) =
    functionApp (TID.getNameFactTag ft) (map ((++) "Term ") (convenienceNames (length fts) "t"))


veriFastClaimEncoding :: Document d => TID.Theory -> d
veriFastClaimEncoding thy = claimDef thy
claimDef :: Document d => TID.Theory -> d
claimDef tamiThy =
    let 
        claims = (collectClaimsIOSFormulas . getDefsFromIOSpecs $ tamiThy)
        factConstructors = map factConstr claims
    in
    ghostBlock $
        text "inductive Claim =" $$
        nest 8 (text (head factConstructors)) $$
        nest 4 (vcat $ map (text . ((++) "|   ")) (tail factConstructors)) <> text ";"
    where
        collectClaimsIOSFormulas :: [TID.IOSFormula] -> [TID.Fact]
        collectClaimsIOSFormulas fs = nubBy TID.eqFactSig $ concat $ map (TID.getFactsFromFormula TID.getClaimsFromIOSTerm) fs
        getDefsFromIOSpecs :: TID.Theory -> [TID.IOSFormula]
        getDefsFromIOSpecs thy = 
            concat $ map ((map snd) . IOS.getAbsPhisWithDef . snd) (IOS.extractIOSpec thy)

persistentFunc :: Document d => [TID.Fact] -> d
persistentFunc facts =
    fixpoint "boolean" "persistent" ["Fact f"] (switchStmt "f" $ map factCase facts)
    where
        factCase :: TID.Fact -> (String, String)
        factCase f@(TID.Fact _ ft fts) =
            let
                isPers = (\fact -> if TID.isFactPers fact then "true" else "false") 
            in
                (functionApp (TID.getNameFactTag ft) (convenienceNames (length fts) "t"), "return " ++ isPers f ++ ";" )

linearFunc :: Document d => d
linearFunc =
    text "fixpoint boolean nonpersistent(Fact f) {" $$
    nest 4 (text "return !persistent(f);") $$
    text "}"


