module PrettyIOSpecs.VeriFast.BytesEncoding (

        veriFastBytesEncoding

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
import              Term.VTerm(constsVTerm)
--import              Term.Builtin.Convenience(x1, x2, x3)
import              Theory.Model.Signature(_sigMaudeInfo)
import qualified    Theory as T

-- Tamigloo imports
-- ---- isabelle generated
import              GenericHelperFunctions(nub, enumIntZero)
import qualified    TamiglooDatatypes as TID
-- ---- other Tamigloo modules
import qualified    PrettyIOSpecs.VeriFast.TermEncoding as VFT
import              PrettyIOSpecs.VeriFast.Utils


veriFastBytesEncoding :: Document d => TID.Theory -> d
veriFastBytesEncoding thy@(TID.Theory _thyName fsig _thyItems) = 
    let
        -- assume maudeSig has been used appropriately to initialize funSyms
        sigMaude = ( _sigMaudeInfo fsig)
    in
        ghostBlock $
            text "fixpoint list<byte> bytes_int(int i);\n" $$
            text "// TODO: Add constructors from other types e.g." $$
            text "// fixpoint list<byte> msgB(string);" $$ text "\n" $$
            constEncoding thy $$ text "\n" $$
            bytesFuncEncoding sigMaude $$ text "\n" $$
            eqEncoding sigMaude $$ text "\n" $$
            gammaEncoding thy
        

gammaEncoding :: Document d => TID.Theory -> d
gammaEncoding thy@(TID.Theory _thyName _fsig _thyItems) =
    text "// Gamma" $$
    text "fixpoint list<byte> gamma(Term t);" $$
    text "fixpoint Term oneTerm(list<byte> b);" $$
    autoLemmaNoBody "void" "gammaOneTerm" ["list<byte> bs"] "true" "gamma(oneTerm(bs)) == bs" <> text "\n" $$
    text "// homomorphism" $$
    gammaHomomorphism thy

gammaFunSym :: FunSym
gammaFunSym = (NoEq (BC.pack "gamma", (1, Public)))

gammaHomomorphism :: Document d => TID.Theory -> d
gammaHomomorphism thy@(TID.Theory _thyName fsig _thyItems) =
    let
        -- get function signatures from Maude signature
        sigMaude = ( _sigMaudeInfo fsig)
        funcSyms = S.toList (funSyms sigMaude)
    in
        (gammaConstants thy) <> text "\n" $$
        (homomorphismFuncs funcSyms) <> text "\n" $$
        text "// TODO: Add homomorphism axiom for constructors you added yourself e.g." $$
        text "// gamma(msg(string)) == msgB(string)"

homomorphismFuncs :: Document d => [FunSym] -> d
homomorphismFuncs fss =
    vcat $ map (\p -> homomorphismSingleFunc ("gammaLemmaFuncs" ++ show (fst p)) (snd p)) (enumIntZero fss)

homomorphismSingleFunc :: Document d => String -> FunSym -> d
homomorphismSingleFunc lemmaName fs =
    let
        args = map (TID.varToVTerm . TID.createLVarFromName) (auxArgs fs)
        termFuncApp = termViewToTerm (FApp fs args)

        gammaArgs = map (\t -> termViewToTerm (FApp gammaFunSym [t])) args
        gammaApp = termViewToTerm (FApp gammaFunSym [termFuncApp])
        bytesFuncApp = termViewToTerm (FApp (funSymBytes fs) gammaArgs)
    in
        autoLemmaNoBody "void" lemmaName (map (\a -> "Term " ++ prettyVFLNTerm True a) args)
            ("true")
            (prettyVFLNTerm True gammaApp ++ " == " ++ prettyVFLNTerm True bytesFuncApp)

    where
        auxArgs :: FunSym -> [String]
        auxArgs (NoEq (_, (ar, _))) = (convenienceNames ar "t")
        auxArgs _ = (convenienceNames 2 "t")

gammaConstants :: Document d => TID.Theory -> d
gammaConstants thy =
    let
        constants = enumIntZero $ nub (TID.extractConsts thy)
        gammaConsts =
            map
                (\p ->
                    singleGammaConst
                    ("gammaLemmaConstants" ++ show (fst p))
                    (makeNameConst $ snd p))
                constants 
    in
        vcat gammaConsts

    where
        singleGammaConst :: Document d => String -> String -> d
        singleGammaConst lemmaName constName =
            let
                gammaApp = functionApp "gamma" ["pubTerm("++ reservedVeriFastWords constName ++ ")"]
                constant = functionApp (reservedVeriFastWords constName  ++ "B") []
            in
                autoLemmaNoBody "void" lemmaName [] "true" (gammaApp ++ " == " ++ constant)



bytesFuncEncoding :: Document d => MaudeSig -> d
bytesFuncEncoding sigMaude =
    let
        -- get function signatures from Maude signature
        funcSyms = S.toList (funSyms sigMaude)
    in
        text "// function declarations" $$
        VFT.funcDecls "list<byte>" (map funSymBytes funcSyms) $$ text "\n" $$
        bytesFuncACLemmas funcSyms

bytesFuncACLemmas :: Document d => [FunSym] -> d
bytesFuncACLemmas fss = VFT.funcACLemmas ppByteACLemma fss

ppByteACLemma :: Document d => FunSym -> d
ppByteACLemma fs = VFT.nameACLemmas "list<byte>" (funSymNameBytes fs)


eqEncoding :: Document d => MaudeSig -> d
eqEncoding sigMaude = 
    let 
        rrules = map rruleBytes $ S.toList (rrulesForMaudeSig sigMaude)
    in
        vcat $ map (uncurry (VFT.ppRRule "list<byte>")) (zip (convenienceNames (length rrules) "byteFuncLemma") rrules)


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
            fixpointNoBody "list<byte>" (reservedVeriFastWords constName  ++ "B") []





funSymName :: FunSym -> String
funSymName (NoEq (f, (_, _))) = reservedVeriFastWords  (BC.unpack f)
funSymName (AC o) = reservedVeriFastWords  (show o)
funSymName (C EMap) = reservedVeriFastWords  (BC.unpack emapSymString)
funSymName (List) = "list" 


funSymNameBytes :: FunSym -> String
funSymNameBytes fs = (funSymName fs) ++ "B" 

funSymBytes :: FunSym -> FunSym
funSymBytes fs@(NoEq (_, (ar, priv))) = (NoEq (BC.pack (funSymNameBytes fs), (ar, priv)))
funSymBytes fs@(AC _) = (NoEq (BC.pack (funSymNameBytes fs), (2, Public)))
funSymBytes (C EMap) = (C EMap) -- ?
funSymBytes (List) =  (List)

rruleBytes :: RRule T.LNTerm -> RRule T.LNTerm
rruleBytes rrule = fmap lnTermBytes rrule

lnTermBytes :: T.LNTerm -> T.LNTerm
lnTermBytes t = case viewTerm t of
    Lit _       -> t
    FApp (AC o) ts -> auxAC (AC o) ts
    FApp fs ts  -> auxF fs ts
    where
        auxF :: FunSym -> [T.LNTerm] -> T.LNTerm
        auxF fsym terms = termViewToTerm (FApp (funSymBytes fsym) (map lnTermBytes terms))
        auxAC :: FunSym -> [T.LNTerm] -> T.LNTerm
        auxAC fsym@(AC o) terms = case terms of
            [_, _] -> auxF fsym terms
            x:xs -> auxF fsym [x, termViewToTerm (FApp (AC o) xs)]
            _ -> error "AC op cannot have unary or empty args"
        auxAC _ _ = error "auxAC called with non-ac function symbol"


