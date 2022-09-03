module PrettyIOSpecs.VeriFast.Utils (


                reservedVeriFastWords
        ,       printTypeOfLNTerm
        ,       printTypeOfIOSTerm
        ,       ghostBlock
        ,       lemma
        ,       autoLemmaNoBody
        ,       fixpoint
        ,       fixpointNoBody
        ,       switchStmt
        ,       switchStmtDoc

        ,       prettyVFLNTerm
        ,       prettyVFIOSTerm
        ,       prettyVFIOSTermWithType
        ,       prettyFact


        ,       module PrettyIOSpecs.CommonFunctions

    ) where

--
import              Prelude
import qualified    Data.Map as Map
import qualified    Data.ByteString.Char8 as BC

-- Tamarin prover imports
import              Text.PrettyPrint.Class
import              Term.Term.FunctionSymbols
import              Term.Term.Raw
import              Term.LTerm(sortOfLNTerm)
import qualified    Theory as T

-- Tamigloo imports
-- ---- isabelle generated
import              GenericHelperFunctions(nub)
import qualified    TamiglooDatatypes as TID
import qualified    ProtocolFormat as PF
import qualified    InterfaceModel as IM
import qualified    Decomposition as D
import qualified    IoSpecs as IOS
-- ---- other Tamigloo modules
import DerivingInstances()
import PrettyIOSpecs.CommonFunctions


reservedVeriFastWords :: String -> String
reservedVeriFastWords s =
    case s of
        _ | s == "true" -> "ok"
        _ | s == "pair" -> "paired"
        _ | s == "fst" -> "fstTerm"
        _ | s == "snd" -> "sndTerm"
        _ -> id s 

printTypeOfLNTerm :: T.LNTerm -> String
printTypeOfLNTerm term = case term of
    _ | term == TID.varToVTerm IOS.var_rid -> "Term"
    _ | term == TID.varToVTerm IOS.var_s -> "mset<Fact>"
    _ | term == TID.varToVTerm IOS.var_p -> "Place"
    _ | term == TID.varToVTerm IOS.var_pp -> "Place"
    _ | term == TID.varToVTerm IOS.var_rp -> "mset<Fact>"
    _ | term == TID.varToVTerm IOS.var_lp -> "mset<Fact>"
    _ | term == TID.varToVTerm IOS.var_ap -> "mset<Claim>"
    _ -> printTypeOfLSort (sortOfLNTerm term)

printTypeOfIOSTerm :: TID.IOSTerm -> String
printTypeOfIOSTerm iosT = case iosT of
    TID.IOSTermVar term -> printTypeOfLNTerm term
    TID.IOSTermClaims _ -> "mset<Claim>"
    TID.IOSTermFacts _ -> "mset<Fact>"
    TID.IOSTermSetOp _ _ -> "mset<Fact>"



-- wrap == True: wraps strings in constructors for the message type Term (depending on fresh or pub sort)
-- otherwise: id
wrapFreshPub :: Bool -> T.LSort -> String -> String
wrapFreshPub wrap lsort term = 
    if wrap
    then 
        case lsort of
            T.LSortPub -> "pubTerm(" ++ term ++ ")"
            T.LSortFresh -> "freshTerm(" ++ term ++ ")"
            _ -> term
    else term

-- TODO can possibly simplify the following prettyTerm functions

prettyLit :: Bool -> T.Lit T.Name T.LVar -> String
prettyLit wrap literal = case literal of
    T.Var v -> wrapFreshPub wrap (sortOfLNTerm $ TID.varToVTerm v) (prettyLiteral literal)
    T.Con _ -> wrapFreshPub wrap T.LSortPub (prettyLiteral literal) -- constants are encoded as Pub
    where
        prettyLiteral :: T.Lit T.Name T.LVar -> String
        prettyLiteral (T.Con c) = (reservedVeriFastWords (makeNameConst c)) ++ "()"
        prettyLiteral (T.Var v) = reservedVeriFastWords (IOS.makeNameLVar v)

prettyVFLNTerm :: Bool -> T.LNTerm -> String
prettyVFLNTerm wrap term = prettyVFTerm (prettyLit wrap) term

prettyFact :: Bool -> TID.Fact -> String
prettyFact wrap fact = prettyFactGeneric (prettyVFLNTerm wrap) fact

prettyVFIOSTerm :: Document d => Bool-> TID.IOSTerm -> d
prettyVFIOSTerm wrap term = prettyVFIOSTermGeneric (prettyVFLNTerm wrap) term

prettyVFIOSTermWithType :: Document d => TID.IOSTerm -> d
prettyVFIOSTermWithType t =
    text (printTypeOfIOSTerm t ++ " ") <> prettyVFIOSTerm False t

prettyVFIOSTermGeneric :: Document d => (T.LNTerm -> String) -> TID.IOSTerm -> d
prettyVFIOSTermGeneric prTerm term = case term of
    TID.IOSTermVar lnTerm -> text (prTerm lnTerm)
    TID.IOSTermClaims claims -> (msetFacts $ map (text . (prettyFactGeneric prTerm)) claims)
    TID.IOSTermFacts facts -> (msetFacts $ map (text . (prettyFactGeneric prTerm)) facts)
    TID.IOSTermSetOp op iosTerms -> (prettySetOp prTerm op iosTerms)
    where
        prettySetOp :: Document d => (T.LNTerm -> String) -> TID.SetOpId -> [TID.IOSTerm] -> d
        prettySetOp g opId terms = case opId of
            TID.UpdateSt -> text "U(" <> (hcat $ punctuate (text ", ") (map (prettyVFIOSTermGeneric g) terms)) <> text ")"
            TID.MDiff -> expectsBin terms (
                                functionAppDocMLine (text "msetMinus")
                                [(prettyVFIOSTermGeneric g $ head terms), (prettyVFIOSTermGeneric g $ last terms)]
                        )
            TID.MUnion -> expectsBin terms (
                                functionAppDocMLine (text "msetUnion")
                                [(prettyVFIOSTermGeneric g $ head terms), (prettyVFIOSTermGeneric g $ last terms)]
                        )



-- | Pretty print a term.
prettyVFTerm :: Show l => (l -> String) -> Term l -> String
prettyVFTerm ppLit = ppTerm
  where
    ppTerm t = case viewTerm t of
        Lit l                                     -> ppLit l
        FApp (AC o)        ts                     -> auxAC (AC o) ts
        FApp (NoEq (f, _)) ts                     -> ppFunBC f ts
        FApp (C EMap)      ts                     -> ppFunBC emapSymString ts
        FApp List          ts                     -> ppFun "list" ts

    ppFunBC f ts = ppFun (BC.unpack f) ts

    ppFun f ts = 
        functionApp (reservedVeriFastWords f) (map ppTerm ts)

    auxAC (AC o) ts = case ts of
        [a] -> ppTerm a
        [a, b] -> ppFun (show o) [a, b]
        x:xs -> ppFun (show o) [x, termViewToTerm (FApp (AC o) xs)]
        _ -> error "AC op cannot have empty args"
    auxAC _ _ = error "auxAC called with non-ac function symbol"



ghostBlock :: Document d => d -> d
ghostBlock body = text "/*@" $$ text "\n" $$ nest 4 body $$ text "@*/"


msetFacts :: Document d => [d] -> d
msetFacts factList =
        text "msetList(" $$
        nest 4 ( foldr (\x y -> text "cons(" <> x <> text "," $$ y <> text ")") (text "nil") factList ) $$
        text ")"

lemma :: Document d => d -> d -> [d] -> d -> d -> d -> d
lemma ret name args req ens body =
        (functionAppDoc (text "lemma " <> ret <> text " " <> name) args) $$
        nest 4 (text "requires " <> req <> text ";") $$ 
        nest 4 (text "ensures " <> ens <> text ";") $$
        text "{" $$
        nest 4 body $$
        text "}"

autoLemmaNoBody :: Document d => String -> String -> [String] -> String -> String -> d
autoLemmaNoBody ret name args req ens =
        text (functionApp ("lemma_auto " ++ ret ++ " " ++ name) args ++ ";") $$
        nest 4 (text $ "requires " ++ req ++ ";") $$ 
        nest 4 (text $ "ensures " ++ ens ++ ";")

fixpoint :: Document d => String -> String -> [String] -> d -> d
fixpoint ret name args body =
        text (functionApp ("fixpoint " ++ ret ++ " " ++ name) args ++ " {") $$
        nest 4 body $$
        text "}"

fixpointNoBody :: Document d => String -> String -> [String] -> d
fixpointNoBody ret name args =
        text (functionApp ("fixpoint " ++ ret ++ " " ++ name) args ++ ";")

switchStmt :: Document d => String -> [(String, String)] -> d
switchStmt switchOn cases =
    text ("switch (" ++ switchOn ++ ") {") $$
    nest 4 (vcat $ map (uncurry caseStmt) cases) $$
    text "}"

caseStmt :: Document d => String -> String -> d
caseStmt caseId caseBody = text ("case " ++ caseId ++ ": " ++ caseBody)

switchStmtDoc :: Document d => d -> [(d, d)] -> d
switchStmtDoc switchOn cases =
    text "switch (" <> switchOn <> text ") {" $$
    nest 4 (vcat $ map (uncurry caseStmtDoc) cases) $$
    text "}"


caseStmtDoc :: Document d => d -> d -> d
caseStmtDoc caseId caseBody = text "case " <> caseId <> text ": " $$ nest 4 caseBody