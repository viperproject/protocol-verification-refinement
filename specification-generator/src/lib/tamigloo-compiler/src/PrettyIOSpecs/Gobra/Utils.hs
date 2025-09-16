module PrettyIOSpecs.Gobra.Utils (

        gobraFilePathRel
    ,   gobraFilePathBase
    ,   modNames
    ,   reservedGobraWords

    ,   prettyLit
    ,   prettyGobraLNTerm
    ,   prettyGobraLNTermWithType
    ,   prettyGobraIOSTerm
    ,   TriggerSetting(..)
    ,   gobraHeader
    ,   domain

    ,   exists
    ,   forallWithTriggerSetting
    ,   forallWithTriggerSettingInline

    ,   axiom
    ,   prettyFact
    ,   prettyGobraIOSTermWithType
    ,   prettyGobraIOSTermGeneric

    ,   printDebug
    ,   prettyTamiTheory
    ,   prettyProtocolFormat
    ,   prettyInterfaceModel
    ,   prettyDecomposition
    ,   prettyPermissions

    ,   printTypeOfIOSTerm
    ,   wrapFreshPub

    ,   module PrettyIOSpecs.CommonFunctions


    ) where

--
import              Prelude
import qualified    Data.Map as Map
import qualified    Data.ByteString.Char8 as BC
import              System.FilePath

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

gobraFilePathRel :: String -> String
gobraFilePathRel name = name </> (name ++ ".gobra")

gobraFilePathBase :: Map.Map String String -> String -> String
gobraFilePathBase config name = config Map.! "base_dir" </> (gobraFilePathRel name)

modNames :: [String]
modNames =             
    [ "place"
    , "fresh"
    , "pub"
    , "term"
    , "bytes"
    , "claim"
    , "fact"
    , "iospec"
    ]

data TriggerSetting = None | Lhs | All
    deriving (Prelude.Read, Prelude.Show, Prelude.Eq)

{-  can be used to resolve overlap between 
    names declared in Tamarin (e.g. function names) and reserved gobra keywords -}
reservedGobraWords :: String -> String
reservedGobraWords "true" = "ok"
reservedGobraWords notReserved = notReserved

printTypeOfLNTerm :: T.LNTerm -> String
printTypeOfLNTerm term = case term of
    _ | term == TID.varToVTerm IOS.var_rid -> "Term"
    _ | term == TID.varToVTerm IOS.var_s -> "mset[Fact]"
    _ | term == TID.varToVTerm IOS.var_p -> "Place"
    _ | term == TID.varToVTerm IOS.var_pp -> "Place"
    _ | term == TID.varToVTerm IOS.var_rp -> "mset[Fact]"
    _ | term == TID.varToVTerm IOS.var_lp -> "mset[Fact]"
    _ | term == TID.varToVTerm IOS.var_ap -> "mset[Claim]"
    _ -> printTypeOfLSort (sortOfLNTerm term)

printTypeOfIOSTerm :: TID.IOSTerm -> String
printTypeOfIOSTerm iosT = case iosT of
    TID.IOSTermVar term -> printTypeOfLNTerm term
    TID.IOSTermClaims _ -> "mset[Claim]"
    TID.IOSTermFacts _ -> "mset[Fact]"
    TID.IOSTermSetOp _ _ -> "mset[Fact]"


{- pretty printing IOSFormulas -}

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

prettyLit :: Bool -> T.Lit T.Name T.LVar -> String
prettyLit wrap literal = case literal of
    T.Var v -> wrapFreshPub wrap (sortOfLNTerm $ TID.varToVTerm v) (prettyLiteral literal)
    T.Con _ -> wrapFreshPub wrap T.LSortPub (prettyLiteral literal) -- constants are encoded as Pub
    where
        prettyLiteral :: T.Lit T.Name T.LVar -> String
        prettyLiteral (T.Con c) = (reservedGobraWords (makeNameConst c)) ++ "()"
        prettyLiteral (T.Var v) = reservedGobraWords (IOS.makeNameLVar v)

prettyGobraLNTerm :: Bool -> T.LNTerm -> String
prettyGobraLNTerm wrap term = prettyGobraTerm (prettyLit wrap) term 

prettyGobraLNTermWithType :: T.LNTerm -> String
prettyGobraLNTermWithType lnTerm = prettyGobraLNTerm False lnTerm ++ " " ++ printTypeOfLNTerm lnTerm

prettyFact :: Bool -> TID.Fact -> String
prettyFact wrap fact = prettyFactGeneric (prettyGobraLNTerm wrap) fact

prettyGobraIOSTerm :: Document d => Bool-> TID.IOSTerm -> d
prettyGobraIOSTerm wrap term = prettyGobraIOSTermGeneric (prettyGobraLNTerm wrap) term

prettyGobraIOSTermGeneric :: Document d => (T.LNTerm -> String) -> TID.IOSTerm -> d
prettyGobraIOSTermGeneric prTerm term = case term of
    TID.IOSTermVar lnTerm -> text (prTerm lnTerm)
    TID.IOSTermClaims claims -> text (printTypeOfIOSTerm term ++ " {") $$ nest 4 (prettyFacts (prettyFactGeneric prTerm) claims) <> text "}"
    TID.IOSTermFacts facts -> text (printTypeOfIOSTerm term ++ " {") $$ nest 4 (prettyFacts (prettyFactGeneric prTerm) facts) <> text "}"
    TID.IOSTermSetOp op iosTerms -> (prettySetOp prTerm op iosTerms)
    where
        prettySetOp :: Document d => (T.LNTerm -> String) -> TID.SetOpId -> [TID.IOSTerm] -> d
        prettySetOp g opId terms = case opId of
            TID.UpdateSt -> text "U(" <> (hcat $ punctuate (text ", ") (map (prettyGobraIOSTermGeneric g) terms)) <> text ")"
            TID.MDiff -> expectsBin terms ((prettyGobraIOSTermGeneric g $ head terms) <> text " setminus " <> (prettyGobraIOSTermGeneric g $ last terms))
            TID.MUnion -> expectsBin terms ((prettyGobraIOSTermGeneric g $ head terms) <> text " union " <> (prettyGobraIOSTermGeneric g $ last terms))


prettyGobraIOSTermWithType :: Document d => TID.IOSTerm -> d
prettyGobraIOSTermWithType t =
    prettyGobraIOSTerm False t <> text (" " ++ printTypeOfIOSTerm t)






-- | Pretty print a term.
prettyGobraTerm :: Show l => (l -> String) -> Term l -> String
prettyGobraTerm ppLit = ppTerm
  where
    ppTerm t = case viewTerm t of
        Lit l                                     -> ppLit l
        FApp (AC o)        ts                     -> auxAC (AC o) ts
        FApp (NoEq (f, _)) ts                     -> ppFunBC f ts
        FApp (C EMap)      ts                     -> ppFunBC emapSymString ts
        FApp List          ts                     -> ppFun "list" ts

    ppFunBC f ts = ppFun (BC.unpack f) ts

    ppFun f ts = 
        (reservedGobraWords f) ++"(" ++ joinString ", " (map ppTerm ts) ++ ")"

    auxAC (AC o) ts = case ts of
        [a] -> ppTerm a
        [a, b] -> ppFun (show o) [a, b]
        x:xs -> ppFun (show o) [x, termViewToTerm (FApp (AC o) xs)]
        _ -> error "AC op cannot have empty args"
    auxAC _ _ = error "auxAC called with non-ac function symbol"



{- pretty printing Tamigloo theories and steps -}

printDebug :: Document d => TID.Theory -> d
printDebug thy =
    prettyTamiTheory thy $$
    prettyProtocolFormat thy $$
    prettyInterfaceModel thy $$
    prettyDecomposition thy $$
    prettyPermissions thy


prettyProtocolFormat :: Document d => TID.Theory -> d
prettyProtocolFormat thy = 
    ($$)    (text "==== Protocol Format ==========\n")
            (nest 4 $ 
                (text "Fact signature Environment" $$ (nest 4 $ vcat $ map (text .  showTamiFactTag) $ PF.factSigEnv thy)) $$ text "\n" $$
                (text "Fact signature Action" $$ (nest 4 $ vcat $ map (text .  showTamiFactTag) $ PF.factSigAct thy)) $$ text "\n" $$
                (text "Fact signature State" $$ (nest 4 $ vcat $ map prettyTamiRoleWithFactTags $ PF.factSigState thy)) $$ text "\n" $$
                (text "Environment Rules" $$ (nest 4 $ vcat $ map prettyTamiRule $ PF.extractEnvRules thy)) $$
                (text "Protocol Rules" $$ (nest 4 $ vcat $ map prettyTamiRoleRule $ PF.extractStateRulesWithRole thy))
            )

prettyInterfaceModel :: Document d => TID.Theory -> d
prettyInterfaceModel thy = 
    ($$)    (text "==== Interface Model ==========\n")
            (nest 4 $ vcat [
                (text "Fact signature Buffer" $$ (nest 4 $ vcat $ map prettyTamiRoleWithFacts $ IM.factSigBuf thy)) $$ text "\n",
                text "Environment Rules minus Setup Rules" $$ (nest 4 $ vcat $ map prettyTamiRule $ IM.extractEnvMinusRules thy),
                text "IO Rules" $$ (nest 4 $ vcat $ map prettyTamiRoleRule $ mergeTriplet $ IM.extractIoRulesWithRole thy),
                text "Protocol Rules with rid" $$ (nest 4 $ vcat $ map prettyTamiRoleRule $ IM.extractStateRulesWithRid thy)
                ]
            )
    where
        mergeTriplet :: ([a], ([a], [a])) -> [a] 
        mergeTriplet t = (fst t) ++ (fst (snd t)) ++ (snd (snd t)) 

prettyDecomposition :: Document d => TID.Theory -> d
prettyDecomposition thy = 
    ($$)    (text "==== Decomposition ==========\n")
            (nest 4 $ vcat [
                text "Environment Rules minus Setup Rules same as before" ,
                text "Protocol Rules with rid same as before" ,
                text "Environment part of IO Rules" $$ (nest 4 $ vcat $ map prettyTamiRule splitEnvIoRules),
                text "Protocol part of Io Rules" $$ (nest 4 $ vcat $ map prettyTamiRoleRule $ splitProtoIoInRules++splitProtoIoOutRules)
                ]
            )
    where
        splitEnvIoRules = fst (D.extractIoEnvAndIoProtoRules thy)
        splitProtoIoInRules = fst (snd (D.extractIoEnvAndIoProtoRules thy))
        splitProtoIoOutRules = snd (snd (D.extractIoEnvAndIoProtoRules thy))

prettyPermissions :: Document d => TID.Theory -> d
prettyPermissions thy = 
    let
        formulas =
            concatMap (\inp -> map snd $ IOS.getAbsPhisWithDef (snd inp)) (IOS.extractIOSpec thy)
        perms = 
            nub $ map TID.accPredOpId $ 
                TID.filterIOSFpredsFromFormulas 
                    TID.isPerm
                    formulas
    in
        (text "==== Permissions ====") $$
        (nest 4 $ vcat $ map (text . show) perms)


prettyTamiRoleWithFactTags :: Document d => (String, [TID.FactTag]) -> d
prettyTamiRoleWithFactTags (role, fts) =
    text (role ++ ":") $$
    (nest 4 $ vcat $ map (text . showTamiFactTag) fts)

prettyTamiTheory :: Document d => TID.Theory -> d
prettyTamiTheory thy@(TID.Theory thyName fsig _thyItems) = 
    (text thyName) $$
    (nest 4 (text $ show fsig)) <> (text "\n") $$
    (nest 4 (prettyTamiRules $ TID.extractRules thy))

prettyTamiRules :: Document d => [TID.Rule] -> d
prettyTamiRules rs = vcat $ punctuate (text "\n") $ map prettyTamiRule rs

prettyTamiRoleRule :: Document d => (String, TID.Rule) -> d
prettyTamiRoleRule (role, rule) = (text $ show role) $$ prettyTamiRule rule

prettyTamiRule :: Document d => TID.Rule -> d
prettyTamiRule (TID.Rule rg name pr ac cncl) = 
    text ("rule " ++ name ++ " " ++ show rg ++ ":") $$
    (nest 4 $
        text "Pr:" $$ (nest 4 $ prettyTamiFacts pr) $$ 
        text "Ac:" $$ (nest 4 $ prettyTamiFacts ac) $$ 
        text "Cncl:" $$ (nest 4 $ prettyTamiFacts cncl)
    ) $$ text "\n"

prettyTamiRoleWithFacts :: Document d => (String, [TID.Fact]) -> d
prettyTamiRoleWithFacts (role, fs) =
    text (role ++ ":") $$
    (nest 4 $ prettyTamiFacts fs)

prettyTamiFacts :: Document d => [TID.Fact] -> d
prettyTamiFacts fs = vcat (map prettyTamiFact fs)

prettyTamiFact :: Document d => TID.Fact -> d
prettyTamiFact (TID.Fact fg ft fts) = 
    text (showTamiFactTag ft) $$
    (text "|  (") <> (text $ joinString ", " $ map (prettyGobraLNTerm True) fts) <> text ")" $$
    (text "|  ") <> (text $ show fg)

showTamiFactTag :: TID.FactTag -> String
showTamiFactTag ft = case ft of
    (TID.StateFact m role step ar) -> (multipString m) ++ "(St)_" ++ role ++ "_" ++ (show step) ++ "/" ++ (show ar)
    (TID.SetupFact m role ar) -> (multipString m) ++ "(Setup)_" ++ role ++ "/" ++ (show ar)
    (TID.ProtoFact m name ar) -> (multipString m) ++ "(Proto)_"++name ++ "/" ++ (show ar)
    (TID.FreshFact) -> "Fr" ++ "/1"
    (TID.InFact) -> "In" ++ "/1"
    (TID.OutFact) -> "Out" ++ "/1"
    _ -> error "Should not need to show internal fact tag."
    where
        multipString :: T.Multiplicity -> String
        multipString x = case x of
                    T.Linear     -> ""
                    T.Persistent -> "!"

{- Formatting -}

gobraHeader :: Document d => Map.Map String String -> String -> [String] -> d -> d
gobraHeader config packageName importedPackages spec = 
    packageHeader packageName $$
    (text "\n") $$
    importHeader config importedPackages $$
    (text "\n") $$
    spec

packageHeader :: Document d => String -> d
packageHeader package_name = 
    text (
      "package " ++ package_name ++ "\n"
    )

importHeader :: Document d => Map.Map String String -> [String] -> d
importHeader config importedPackages =
    vcat $ map (text . ("import . " ++)) $ map (\i -> quotes' $ config Map.! "module" </> i) importedPackages 
    where
        quotes' :: String -> String
        quotes' s = "\""++s++"\""

domain :: Document d => String -> d -> d
domain name doc = 
    braces' (text ("ghost type " ++ name ++ " domain")) doc


forallWithTriggerSetting :: Document d => TriggerSetting -> d -> [d] -> d -> d
forallWithTriggerSetting =
    quantifiedWithTriggerSetting False "forall"

forallWithTriggerSettingInline :: Document d => TriggerSetting -> d -> [d] -> d -> d
forallWithTriggerSettingInline =
    quantifiedWithTriggerSetting True "forall"

exists :: Document d => d -> d -> d
exists termsWithType body = quantifiedWithTriggerSetting False "exists" None termsWithType [] body

quantifiedWithTriggerSetting :: Document d => Bool -> String -> TriggerSetting -> d -> [d] -> d -> d
quantifiedWithTriggerSetting inline quant triggerSetting termsWithType triggers body =
    let
        triggs = 
            if (length triggers) == 0 || triggerSetting == None
            then []
            else (
                if triggerSetting == Lhs
                then (take 1 triggers)
                else triggers 
            )
    in
        if inline
        then quantifiedInline quant termsWithType triggs body
        else quantified quant termsWithType triggs body

quantified :: Document d => String -> d -> [d] -> d -> d
quantified quant termsWithType triggers body =
    let
        bracedTriggers = (hcat $ punctuate (text " ") $ map bracesInline triggers)
    in
        text (quant ++ " ") <> termsWithType <> text " :: " $$
        nest 4 (
            bracedTriggers <> text " (" $$
            nest 4 body <> text ")"
        )

quantifiedInline :: Document d => String -> d -> [d] -> d -> d
quantifiedInline quant termsWithType triggers body =
    let
        bracedTriggers = (hcat $ punctuate (text " ") $ map bracesInline triggers)
    in
        text (quant ++ " ") <> termsWithType <> text " :: " <>
        bracedTriggers <> text " (" <>
        body <> text ")"


axiom :: Document d => d -> d
axiom body = braces' (text "axiom ") body

braces' :: Document d => d -> d -> d
braces' header body = header <> text " {" $$ nest 4 body $$ text "}"