module PrettyIOSpecs.Gobra.FactEncoding (

          gobraFactEncoding
        , gobraClaimEncoding

  ) where

--
import              Prelude
import qualified    Data.Map as Map

-- Tamarin prover imports
import              Text.PrettyPrint.Class

-- Tamigloo imports
-- ---- isabelle generated
import              GenericHelperFunctions(nubBy, flipEnumIntZero)
import qualified    TamiglooDatatypes as TID
import qualified    IoSpecs as IOS
-- ---- other Tamigloo modules
import              PrettyIOSpecs.Gobra.Utils

{- included are fact encoding, claim encoding -}

gobraFactEncoding :: Document d => Map.Map String String -> TID.Theory -> d
gobraFactEncoding config tamiThy =
    gobraHeader config "fact" ["mod_term", "mod_pub", "mod_fresh"] (
        domain "Fact" (
            factEncoding (collectFactsIOSFormulas . getDefsFromIOSpecs $ tamiThy) <>
            (text "\n") 
        ) $$
        hardcoded
    )
    where
        factEncoding :: Document d => [TID.Fact] -> d
        factEncoding fs =
            (vcat $ punctuate (text "\n") $
                map (uncurry singleFactEncoding) (flipEnumIntZero  fs)) <>
            text "\n" $$
            persistentFunc (flipEnumIntZero  fs)
        collectFactsIOSFormulas :: [TID.IOSFormula] -> [TID.Fact]
        collectFactsIOSFormulas fs = nubBy TID.eqFactSig $ concat $ map (TID.getFactsFromFormula TID.getFactsFromIOSTerm) fs
        getDefsFromIOSpecs :: TID.Theory -> [TID.IOSFormula]
        getDefsFromIOSpecs thy = 
            concat $ map ((map snd) . IOS.getAbsPhisWithDef . snd) (IOS.extractIOSpec thy)


gobraClaimEncoding :: Document d => Map.Map String String -> TID.Theory -> d
gobraClaimEncoding config tamiThy =
    gobraHeader config "claim" ["mod_term"] (
        domain "Claim" (
            claimEncoding (collectClaimsIOSFormulas . getDefsFromIOSpecs $ tamiThy) <>
            (text "\n")
        )
    )
    where
        claimEncoding :: Document d => [TID.Fact] -> d
        claimEncoding fs = 
            (vcat $ punctuate (text "\n") $ map singleClaimEncoding fs) <> text "\n" 
        collectClaimsIOSFormulas :: [TID.IOSFormula] -> [TID.Fact]
        collectClaimsIOSFormulas fs = nubBy TID.eqFactSig $ concat $ map (TID.getFactsFromFormula TID.getClaimsFromIOSTerm) fs
        getDefsFromIOSpecs :: TID.Theory -> [TID.IOSFormula]
        getDefsFromIOSpecs thy = 
            concat $ map ((map snd) . IOS.getAbsPhisWithDef . snd) (IOS.extractIOSpec thy)


persistentFunc :: Document d => [(TID.Fact, Integer)] -> d
persistentFunc inp =
    let
        functionDeclarations = 
            text "// each fact has a unique tag:" $$
            text (functionDef "getTag" ["f Fact"] "int") <> text "\n" $$
            text (functionDef "persistent" ["f Fact"] "bool") 
        termsWithType = text "f Fact"
        triggers = [text (functionApp "persistent" ["f"])]
    in
        if length persistentFactTags == 0
        then functionDeclarations
        else
            functionDeclarations $$
            axiom (
                forallWithTriggerSetting All termsWithType triggers body
            )
    where
        persistentFactTags :: [Integer]
        persistentFactTags = map snd $ filter (\p -> TID.isFactPers (fst p)) inp
        body :: Document d => d
        body = 
            let
                getTagApp = functionApp "getTag" ["f"]
                persistentTagsOr = 
                    hcat . punctuate (text " || ") $ 
                        map (\t -> text (getTagApp ++ " == " ++ (show t))) persistentFactTags
            in
                text (functionApp "persistent" ["f"]) <>
                text " ==" $$
                parens persistentTagsOr


{- encoding for a single fact i.e. constructor, destructor, tag (discriminator) -}
singleFactEncoding :: Document d => TID.Fact -> Integer -> d
singleFactEncoding f tag =
    let
        constr = fst (factConstrDestrDef f "Fact")
        destr = snd (factConstrDestrDef f "Fact") 
    in
        text ("// tag " ++ (show tag)) $$
        constr $$
        destr $$
        factInjWithTag f True tag

{- encoding for a single action fact / claim i.e. constructor, destructor, injectivity) 
    We only distinguish facts and claims by where they appear in a rule l ->_a r.
    l,r for facts; a for claims; The type however is always TID.Fact (also for claims). 
    Thus we can resuse large parts of the code. -}
singleClaimEncoding :: Document d => TID.Fact -> d
singleClaimEncoding f =
    let 
        constr = fst (factConstrDestrDef f "Claim")
        destr = snd (factConstrDestrDef f "Claim")
    in
        constr $$
        destr $$
        factInjWithTag f False (-1)



{- constructor and desctructor to encode a Fact -}
factConstrDestrDef :: Document d => TID.Fact -> String -> (d, d)
factConstrDestrDef (TID.Fact _ ft fts) retType =
    let 
        name = (TID.getNameFactTag ft)
        argType = (if ft == TID.FreshFact then "Fresh" else "Term")
        args = map (++ (" " ++ argType)) (convenienceNames (length fts) "t")
    in
        (text (functionDef name args retType), 
        text (functionDef ("get" ++ name) ["f " ++ retType] (if length fts == 1 then argType else "seq[" ++ argType ++ "]")))
{- It may be necessary to have a destructor for each argument instead of destructing to a sequence of arguments-}
{-
factDestructorsDef :: TID.Fact -> d
factDestructorsDef f@(TID.Fact _ ft fts)  = 
    let 
        name = (TID.getNameFactTag ft)
        argType = (if ft == TID.FreshFact then "Fresh" else "Term")
        destrNames = zipWith (++) (convenienceNames (length fts) "get") (repeat name)
    in
        vcat $ map (\n -> functionDef n ["f: Fact"] argType) destrNames
-}


factConstrApp :: TID.Fact -> [String] -> String
factConstrApp f@(TID.Fact _ ft fts) args =
    let name = (TID.getNameFactTag ft)
    in
        if length fts /= length args
        then error $ "length of fact arguments unequal to length of provided args in factConstrApp " ++ show f ++ show args
        else (functionApp name args)
factDestrApp :: TID.Fact -> String -> String
factDestrApp (TID.Fact _ ft _) arg =
    let name = "get" ++ (TID.getNameFactTag ft)
    in
        (functionApp name [arg])      




factInjWithTag :: Document d => TID.Fact -> Bool -> Integer -> d
factInjWithTag f@(TID.Fact _ ft fts) withTag tag = 
    let
        argType = (if ft == TID.FreshFact then "Fresh" else "Term")
        termsWithType =
            joinString ", " $ map (++ (" " ++ argType)) (convenienceNames (length fts) "t") 
        -- constructor as trigger
        triggers = [text (factConstrApp f terms)]
    in
    axiom (
        forallWithTriggerSetting All (text termsWithType) triggers body
    )
    where
        terms :: [String]
        terms = convenienceNames (length fts) "t"
        body :: Document d => d
        body = 
            let
                argType = (if ft == TID.FreshFact then "Fresh" else "Term")
            in
                text (factDestrApp f (factConstrApp f terms)) <>
                text " ==" $$
                text
                (if length fts == 1
                    then head terms
                    else "seq[" ++ argType ++"]{" ++ (joinString ", " terms) ++ "}") <>
                (if withTag
                    then getTagCheck (factConstrApp f terms) tag
                    else emptyDoc)
        getTagCheck :: Document d => String -> Integer -> d
        getTagCheck constr tagArg =
            text " &&" $$
            text (functionApp "getTag" [constr]) <>
            text (" == " ++ show tagArg)


{- Hardcoded M, U, persistentFacts, linearFacts -}
hardcoded :: Document d => d
hardcoded =
    filterIsPersFunc <> text "\n" $$
    filterIsLinFunc <> text "\n" $$
    mFunc <> text "\n" $$
    uFunc

{- ---- M(l, s) -}
{- part of the guard condition in an IO spec: ensures that l is a subset of s -}
mFunc :: Document d => d
mFunc = 
    text "ghost" $$
    text "ensures res == (linearFacts(l) subset s && persistentFacts(l) subset s)" $$
    text "pure func M(l mset[Fact], s mset[Fact]) (res bool) {" $$
    nest 4 (
        text "// non-persistent facts" $$
        text "return linearFacts(l) subset s &&" $$
        nest 4 (
            text "// persistent facts" $$
            text "persistentFacts(l) subset s"
        )
    ) $$
    text "}"

{- ---- U(l,r,s) -}
{- update the state s in an IO spec-}
uFunc :: Document d => d
uFunc = 
    text "ghost" $$
    text "ensures result == s setminus linearFacts(l) union r" $$
    text "pure func U(l mset[Fact], r mset[Fact], s mset[Fact]) (result mset[Fact])"

{- ---- -}
{- filters a multiset of facts so that only persistent facts remain -}
filterIsPersFunc :: Document d => d
filterIsPersFunc =
    text "ghost" $$
    text "// returns a multiset containing just the persistent facts of l all with multiplicity 1" $$
    text "ensures forall f Fact :: { f # result } (f # result) == (persistent(f) && (f # l) > 0 ? 1 : 0)" $$
    text "pure func persistentFacts(l mset[Fact]) (result mset[Fact])"

{- ---- -}
{- filters a multiset of facts so that only linear/non-persistent facts remain -}
filterIsLinFunc :: Document d => d
filterIsLinFunc =
    text "ghost" $$
    text "// returns a multiset containing just the non-persistent facts of l while retaining their multiplicity" $$
    text "ensures forall f Fact :: { f # result } (f # result) == (persistent(f) ? 0 : (f # l))" $$
    text "pure func linearFacts(l mset[Fact]) (result mset[Fact])"



