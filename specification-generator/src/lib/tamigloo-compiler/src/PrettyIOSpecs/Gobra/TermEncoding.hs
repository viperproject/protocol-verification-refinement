module PrettyIOSpecs.Gobra.TermEncoding (

          gobraTermEncoding
        , gobraPubEncoding
        , gobraFreshEncoding
        , gobraPlaceEncoding
  ) where

--
import Prelude
import qualified    Data.Map as Map
import qualified    Data.Set as S
import qualified    Data.ByteString.Char8 as BC

-- Tamarin prover imports
import              Text.PrettyPrint.Class
import              Term.Term.Raw
import              Term.Maude.Signature(MaudeSig, rrulesForMaudeSig, funSyms)
import              Term.Term.FunctionSymbols
import              Term.Builtin.Rules(RRule(..))
import              Term.LTerm (frees)
import              Term.VTerm(constsVTerm)
import              Term.Builtin.Convenience(x1, x2, x3)
import              Theory.Model.Signature(_sigMaudeInfo)
import qualified    Theory as T

-- Tamigloo imports
-- ---- isabelle generated
import              GenericHelperFunctions(nub)
import qualified    TamiglooDatatypes as TID
-- ---- other Tamigloo modules
import              PrettyIOSpecs.Gobra.Utils


{- included are term encoding, pub encoding, fresh encoding, place encoding -}

{- term encoding -}
gobraTermEncoding :: Document d => Map.Map String String -> TID.Theory -> d
gobraTermEncoding config (TID.Theory _thyName fsig _thyItems) = 
    let
        -- assume maudeSig has been used appropriately to initialize funSyms
        sigMaude = ( _sigMaudeInfo fsig)
    in
        gobraHeader config "term" ["pub", "fresh"] (
            domain "Term" (
                baseTermEncoding $$
                termFuncEncoding sigMaude $$
                eqEncoding (read (config Map.! "triggers") :: TriggerSetting) sigMaude
            )
        )

{- ---- term function encoding -}
{-  Tamarin allows for the declaration of functions. 
    The functions are represented in the Maude signature of a Tamarin theory.
    Naturally, these also have to be included in the gobra specification. -}
termFuncEncoding :: Document d => MaudeSig -> d
termFuncEncoding sigMaude =
    let
        -- get function signatures from Maude signature
        funcSyms = S.toList (funSyms sigMaude)
    in
        (vcat $ map (ppFunSym "Term") funcSyms) $$ text "\n"

ppFunSym :: Document d => String -> FunSym -> d
ppFunSym typeId (NoEq (f, (ar, _))) = 
    -- we do not make a distinction between private and public since we don't consider the adversary
    let 
        args = map (++ " " ++ typeId) (convenienceNames ar "t")
    in
        text $ functionDef (reservedGobraWords (BC.unpack f)) args typeId
ppFunSym typeId (AC o) = 
    -- AC function symbols are made to be binary
    -- This needs to happen in function declaration and application
    (text $ functionDef (reservedGobraWords (show o)) ["x " ++ typeId, "y " ++ typeId] typeId) $$
    -- text ("// " ++ (reservedGobraWords (show o)) ++ " is associative") $$
    text "// associativity" $$
    assocEncoding (AC o) $$
    -- text ("// " ++ (reservedGobraWords (show o)) ++ " is commutative") $$
    text "// commutativity" $$
    commEncoding (AC o)
ppFunSym typeId (C EMap) = -- TODO not sure if we should print emapSymString or EMap
    text $ functionDef (reservedGobraWords (BC.unpack emapSymString)) ["x " ++ typeId, "y " ++ typeId] typeId 
ppFunSym typeId (List) = -- TODO not sure about this one, but does not seem to be used anyway
    text $ functionDef "list" ["l seq[" ++ typeId ++ "]"] typeId



{-  AC function symbols need an additional axiom to express it.
    We do this by creating an auxiliary rewrite rule (for binary AC op) 
    which will be printed alongside other
    rrules based on the Tamarin equational theory (see equation encoding). -}
{- ---- ---- associativity encoding -}
assocEncoding :: Document d => FunSym -> d
assocEncoding acSym@(AC _) = ppRRule Lhs "Term" (rruleAssoc acSym)
    where 
        rruleAssoc :: FunSym -> RRule T.LNTerm
        rruleAssoc acOp =        auxFapp acOp [x1, auxFapp acOp [x2, x3]]
                          `RRule` auxFapp acOp [auxFapp acOp [x1, x2], x3]
        auxFapp :: FunSym -> [T.LNTerm] -> T.LNTerm
        auxFapp fs ts = termViewToTerm (FApp fs ts)
assocEncoding _ = error "assocEncoding called with non-ac function symbol"

{- ---- ---- commutativity encoding -}
commEncoding :: Document d => FunSym -> d
commEncoding acSym@(AC _) = ppRRule Lhs "Term" (rruleComm acSym)
    where 
        rruleComm :: FunSym -> RRule T.LNTerm
        rruleComm acOp =         termViewToTerm (FApp acOp [x1, x2]) 
                          `RRule` termViewToTerm (FApp acOp [x2, x1])
commEncoding _ = error "commEncoding called with non-ac function symbol"

{- ---- equation encoding -}
{-  The equations declared in Tamarin give semantic to the functions.
    Equations are represented as rewrite rules in the Maude singature
    (and as AC/C in the function symbols).
    In Gobra, we write the rewrite rules as axioms in the Term domain -}
eqEncoding :: Document d => TriggerSetting -> MaudeSig -> d
eqEncoding triggerSetting sigMaude = 
    let 
        rrules = S.toList (rrulesForMaudeSig sigMaude)
    in
        vcat $ punctuate (text "\n") $ map (ppRRule triggerSetting "Term") rrules

{- ---- ---- pretty print rewriting rules -}
ppRRule :: Document d => TriggerSetting -> String -> T.RRule T.LNTerm -> d
ppRRule triggerSetting typeId rr@(T.RRule lhs rhs) = 
    let 
        trigger = (auxTrigger lhs) ++ (auxTrigger rhs)
        body = text (prettyGobraLNTerm True lhs) <> text " == " <> text (prettyGobraLNTerm True rhs)
        vars = frees rr
        doc_vars = sepTerms (map (text . prettyGobraLNTerm True . TID.varToVTerm) vars) <> text (" " ++ typeId)
    in
        if null vars
        then axiom body
        else axiom (forallWithTriggerSetting triggerSetting doc_vars trigger body)
    where
        auxTrigger :: Document d => T.LNTerm -> [d]
        auxTrigger t = case viewTerm t of
            (FApp _ (_:_)) -> [text $ prettyGobraLNTerm True t]
            _ -> [emptyDoc]



{- ---- Pub/Fresh to Term -}
{-  The Fresh and Pub types have to be lifted to Term types by providing constructors.
    This way Fresh and Pub values are usable in expressions requiring Terms -}
baseTermEncoding :: Document d => d
baseTermEncoding =
    text (functionDef "freshTerm" ["f Fresh"] "Term") $$
    text (functionDef "getFreshTerm" ["t Term"] "Fresh") $$
    axiom (
        forallWithTriggerSetting All 
        (text "f Fresh") 
        [text "freshTerm(f)"] 
        (text "getFreshTerm(freshTerm(f)) == f")
    ) $$
    text (functionDef "pubTerm" ["p Pub"] "Term") $$
    text (functionDef "getPubTerm" ["t Term"] "Pub") $$
    axiom (
        forallWithTriggerSetting All 
        (text "p Pub") 
        [text "pubTerm(p)"] 
        (text "getPubTerm(pubTerm(p)) == p")
    ) <> text "\n"

{- pub encoding -}
{-  model a public Tamarin LNTerm e.g. $a in Gobra. 
    Since Tamarin uses only abstract terms, the user has to provide concrete constructors
    from basic types e.g. int, string, etc. -}
gobraPubEncoding :: Document d => Map.Map String String -> TID.Theory -> d
gobraPubEncoding config thy =
    gobraHeader config "pub" [] (
        text "// pub encoding ---------------" $$
        domain "Pub" (
            constEncoding thy $$
            text "// TODO!: Add base constructors as uninterpreted functions" $$
            text "// Example:" $$
            text "func pub_msg(string) Pub" $$
            text "func pub_integer64(uint64) Pub"
            ) $$
        text "\n" 
    )

{- ---- constant encoding -}
{- encode constants as null-ary functions in Pub domain -}
constEncoding :: Document d => TID.Theory -> d
constEncoding thy = 
    let
        constants = nub (TID.extractConsts thy) 
    in
        (vcat $ punctuate (text "\n") $ 
            map (constFuncDef . makeNameConst) constants) <> text "\n" 
    where
        constFuncDef :: Document d => String -> d
        constFuncDef constName =
            text $ functionDef (reservedGobraWords constName) [] "Pub"



{- fresh encoding -}
{-  model a fresh Tamarin LNTerm e.g. ~x in Gobra. 
    Since Tamarin uses only abstract terms, the user has to provide concrete constructors
    from basic types e.g. int, string, etc. -}
gobraFreshEncoding :: Document d => Map.Map String String -> d
gobraFreshEncoding config =
    gobraHeader config "fresh" [] (
        text "// fresh encoding ---------------" $$
        domain "Fresh" (
            text "// TODO!: Add base constructors as uninterpreted functions" $$
            text "// Example:" $$
            text "func fr_msg(string) Fresh" $$
            text "func fr_integer64(uint64) Fresh"
            ) $$
        text "\n"
    )


{- place encoding -}
gobraPlaceEncoding :: Document d => Map.Map String String -> d
gobraPlaceEncoding config =
    gobraHeader config "place" [] (
        text "// place encoding ---------------" $$
        domain "Place" (
            text (functionDef "place" ["p int"] "Place")
        ) $$
        text ("pred " ++ functionApp "token" ["t Place"]) $$
        text "\n"
    )
