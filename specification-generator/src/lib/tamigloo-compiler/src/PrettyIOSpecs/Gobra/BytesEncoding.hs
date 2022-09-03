module PrettyIOSpecs.Gobra.BytesEncoding (

        gobraBytesEncoding

  ) where


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
-- import              Term.VTerm(constsVTerm)
import              Term.Builtin.Convenience(x1, x2, x3)
import              Theory.Model.Signature(_sigMaudeInfo)
import qualified    Theory as T

-- Tamigloo imports
-- ---- isabelle generated
import              GenericHelperFunctions(nub, splitAndGetFst, splitAndGetSnd)
import qualified    TamiglooDatatypes as TID
-- ---- other Tamigloo modules
import              PrettyIOSpecs.Gobra.Utils


-- The Byte encoding for verifast presents a different approach to print the byte function signatures and rrules
-- Here this is achieved by changing the printers (e.g. ppFunSymB, ppRRuleB) while in the verifast case the funsyms and rrules are changed




gobraBytesEncoding :: Document d => Map.Map String String -> TID.Theory -> d
gobraBytesEncoding config thy@(TID.Theory _thyName fsig _thyItems) = 
    let
        -- assume maudeSig has been used appropriately to initialize funSyms
        sigMaude = ( _sigMaudeInfo fsig)
    in
        gobraHeader config "bytes" ["mod_pub", "mod_term"] (
            domain "Bytes" (
                baseEncoding $$
                constEncoding thy $$
                bytesFuncEncoding sigMaude $$
                eqEncoding (read (config Map.! "triggers") :: TriggerSetting) sigMaude
            ) $$ text "\n\n\n" $$
            domain "Gamma" (
                gammaEncoding thy
            )
        )


gammaEncoding :: Document d => TID.Theory -> d
gammaEncoding thy@(TID.Theory _thyName _fsig _thyItems) =
    text "func gamma(Term) Bytes" $$
    text "func oneTerm(Bytes) Term" $$
    text "// totality" $$
    axiom (
        forallWithTriggerSetting
            All
            (text "b Bytes")
            [text "oneTerm(b)"]
            (text "gamma(oneTerm(b)) == b")
    ) $$ text "\n" $$
    text "// homomorphism" $$
    axiom (
        gammaHomomorphism thy $$
        text "// TODO: Add homomorphism axiom for constructors you added yourself e.g." $$
        text "// &&" $$
        text "// (forall s string :: {gamma(msg(s))} gamma(msg(s)) == msgB(s))"
    )

gammaHomomorphism :: Document d => TID.Theory -> d
gammaHomomorphism thy@(TID.Theory _thyName fsig _thyItems) =
    let
        -- get function signatures from Maude signature
        sigMaude = ( _sigMaudeInfo fsig)
        funcSyms = S.toList (funSyms sigMaude)
    in
        (vcat $ punctuate (text " &&") $ (gammaConstants thy) ++ (map homomorphismSingleFunc funcSyms)) $$ text "\n"

homomorphismSingleFunc :: Document d => FunSym -> d
homomorphismSingleFunc fs =
    let
        args = map (TID.varToVTerm . TID.createLVarFromName) (auxArgs fs)
        termFuncApp = termViewToTerm (FApp fs args)
        termFuncAppDoc = text (prettyGobraLNTerm True termFuncApp)
        gammaArgsDoc = map (\t -> text $ functionApp "gamma" [t]) (auxArgs fs)
        gammaApp = functionAppDoc (text "gamma") [termFuncAppDoc]
        byteFuncAppDoc = functionAppDoc (text $ funSymName fs ++ "B") gammaArgsDoc
        body = gammaApp <> text " == " <> byteFuncAppDoc
    in
        text "(" <>
        (if length (auxArgs fs) > 0
        then
            forallWithTriggerSettingInline
                All
                ((sepTerms $ map text (auxArgs fs)) <> text " Term")
                [gammaApp]
                body
        else
            body)
        <> text ")"
    where
        auxArgs :: FunSym -> [String]
        auxArgs (NoEq (_, (ar, _))) = (convenienceNames ar "t")
        auxArgs _ = (convenienceNames 2 "t")
        funSymName :: FunSym -> String
        funSymName (NoEq (f, (_, _))) = reservedGobraWords (BC.unpack f)
        funSymName (AC o) = reservedGobraWords (show o)
        funSymName (C EMap) = reservedGobraWords (BC.unpack emapSymString)
        funSymName (List) = "listB" 

gammaConstants :: Document d => TID.Theory -> [d]
gammaConstants thy =
    let
        constants = nub (TID.extractConsts thy) 
    in
        map (singleGammaConst . makeNameConst) constants 
    where
        singleGammaConst :: Document d => String -> d
        singleGammaConst constName =
            let
                gammaApp = functionAppDoc (text "gamma") [text "pubTerm(" <> text (reservedGobraWords constName) <> text "())"]
                constant = functionAppDoc (text (removeConstantSuffix (reservedGobraWords constName)  ++ "B")) []
            in
                parens (gammaApp <> text " == " <> constant)

baseEncoding :: Document d => d
baseEncoding =
    text "// TODO: Add constructors from other types e.g." $$
    text "// func msgB(string) Bytes" $$ text "\n"

bytesFuncEncoding :: Document d => MaudeSig -> d
bytesFuncEncoding sigMaude =
    let
        -- get function signatures from Maude signature
        funcSyms = S.toList (funSyms sigMaude)
    in
        text "// function declarations" $$
        (vcat $ map (ppFunSymB "Bytes") funcSyms) $$ text "\n"

eqEncoding :: Document d => TriggerSetting -> MaudeSig -> d
eqEncoding triggerSetting sigMaude = 
    let 
        rrules = S.toList (rrulesForMaudeSig sigMaude)
    in
        text "// function equalities" $$
        (vcat $ punctuate (text "\n") $ map (ppRRuleB triggerSetting "Bytes") rrules)


constEncoding :: Document d => TID.Theory -> d
constEncoding thy = 
    let
        constants = nub (TID.extractConsts thy) 
    in
        text "// constants"$$
        (vcat $ 
            map (constFuncDef . makeNameConst) constants) <> text "\n" 
    where
        constFuncDef :: Document d => String -> d
        constFuncDef constName =
            text $ functionDef (removeConstantSuffix (reservedGobraWords constName)  ++ "B") [] "Bytes"

removeConstantSuffix :: String -> String
removeConstantSuffix s =
    if (reverse . splitAndGetFst . reverse) s == "pub"
    then (reverse . splitAndGetSnd . reverse) s
    else s

{- ---- ---- associativity encoding -}
assocEncoding :: Document d => FunSym -> d
assocEncoding acSym@(AC _) = ppRRuleB Lhs "Bytes" (rruleAssoc acSym)
    where 
        rruleAssoc :: FunSym -> RRule T.LNTerm
        rruleAssoc acOp =        auxFapp acOp [x1, auxFapp acOp [x2, x3]]
                          `RRule` auxFapp acOp [auxFapp acOp [x1, x2], x3]
        auxFapp :: FunSym -> [T.LNTerm] -> T.LNTerm
        auxFapp fs ts = termViewToTerm (FApp fs ts)
assocEncoding _ = error "assocEncoding called with non-ac function symbol"

{- ---- ---- commutativity encoding -}
commEncoding :: Document d => FunSym -> d
commEncoding acSym@(AC _) = ppRRuleB Lhs "Bytes" (rruleComm acSym)
    where 
        rruleComm :: FunSym -> RRule T.LNTerm
        rruleComm acOp =         termViewToTerm (FApp acOp [x1, x2]) 
                          `RRule` termViewToTerm (FApp acOp [x2, x1])
commEncoding _ = error "commEncoding called with non-ac function symbol"




ppFunSymB :: Document d => String -> FunSym -> d
ppFunSymB typeId (NoEq (f, (ar, _))) = 
    -- we do not make a distinction between private and public since we don't consider the adversary
    let 
        args = map (++ " " ++ typeId) (convenienceNames ar "t")
    in
        text $ functionDef (reservedGobraWords (BC.unpack f) ++ "B") args typeId
ppFunSymB typeId (AC o) = 
    -- AC function symbols are made to be binary
    -- This needs to happen in function declaration and application
    (text $ functionDef (reservedGobraWords (show o) ++ "B") ["x " ++ typeId, "y " ++ typeId] typeId) $$
    text ("// " ++ (reservedGobraWords (show o) ++ "B") ++ " is associative") $$
    assocEncoding (AC o) $$
    text ("// " ++ (reservedGobraWords (show o) ++ "B") ++ " is commutative") $$
    commEncoding (AC o) $$ text "\n"
ppFunSymB typeId (C EMap) = -- TODO not sure if we should print emapSymString or EMap
    text $ functionDef (reservedGobraWords (BC.unpack emapSymString) ++ "B") ["x " ++ typeId, "y " ++ typeId] typeId 
ppFunSymB typeId (List) = -- TODO not sure about this one, but does not seem to be used anyway
    text $ functionDef "listB" ["l seq[" ++ typeId ++ "]"] typeId



ppRRuleB :: Document d => TriggerSetting -> String -> T.RRule T.LNTerm -> d
ppRRuleB triggerSetting typeId rr@(T.RRule lhs rhs) = 
    let 
        trigger = (auxTrigger lhs) ++ (auxTrigger rhs)
        body = text (prettyGobraLNTermB True lhs) <> text " == " <> text (prettyGobraLNTermB True rhs)
        vars = frees rr
        doc_vars = sepTerms (map (text . prettyGobraLNTermB True . TID.varToVTerm) vars) <> text (" " ++ typeId)
    in
        if null vars
        then axiom body
        else axiom (forallWithTriggerSetting triggerSetting doc_vars trigger body)
    where
        auxTrigger :: Document d => T.LNTerm -> [d]
        auxTrigger t = case viewTerm t of
            (FApp _ (_:_)) -> [text $ prettyGobraLNTermB True t]
            _ -> [emptyDoc]


prettyGobraLNTermB :: Bool -> T.LNTerm -> String
prettyGobraLNTermB wrap = prettyGobraTermB (prettyLit wrap)

-- | Pretty print a term.
prettyGobraTermB :: Show l => (l -> String) -> Term l -> String
prettyGobraTermB ppLit = ppTerm
  where
    ppTerm t = case viewTerm t of
        Lit l                                     -> ppLit l
        FApp (AC o)        ts                     -> auxAC (AC o) ts
        FApp (NoEq (f, _)) ts                     -> ppFunBC f ts
        FApp (C EMap)      ts                     -> ppFunBC emapSymString ts
        FApp List          ts                     -> ppFun "list" ts

    ppFunBC f ts = ppFun (BC.unpack f) ts

    ppFun f ts = 
        (reservedGobraWords f) ++ "B" ++"(" ++ joinString ", " (map ppTerm ts) ++ ")"

    auxAC (AC o) ts = case ts of
        [a] -> ppTerm a
        [a, b] -> ppFun (show o) [a, b]
        x:xs -> ppFun (show o) [x, termViewToTerm (FApp (AC o) xs)]
        _ -> error "AC op cannot have empty args"
    auxAC _ _ = error "auxAC called with non-ac function symbol"


