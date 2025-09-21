
{-# LANGUAGE ViewPatterns #-}

module TamarinToTamigloo(


        changeTheory
    ,   parseStateFactString
    ,   splitStr
    ,   splitRole

) where

--
import              Prelude
import qualified    Data.Map as Map
import              Data.List.Split
import              Data.List(groupBy, sortOn)
import              Data.Either 
import qualified    Data.Set as S

-- Tamarin prover imports
import qualified    Theory as T
-- import              Theory.Model.Signature (SignaturePure)
import qualified    Theory.Model.Fact as F
import qualified    Theory.Model.Rule as R
import qualified    Theory.Model.Restriction as Restr
import qualified    Theory.Model.Formula as Form
import qualified    Theory.Model.Atom as Atom
import              Term.LTerm (LNTerm)
import              Term.Term.Raw(viewTerm) 
import qualified    Theory.Text.Parser.Token as Tok
import              Text.Parsec         hiding ((<|>))

-- Tamigloo imports
-- ---- isabelle generated
import              DerivingInstances()
import qualified    TamiglooDatatypes as TID
import qualified    GenericHelperFunctions as TamiHelper


{-
    TODO
    - check that the following variable names are not used:
        tami p, tami rid, tami s, tami pp, tami lp, tami ap, and tami rp
-}

{-

    We want to transform the output from the tamarin parser to a similar format for the tamigloo-
    compiler that
        a)  Removes information we do not need 
        b)  Performs some checks and categorizations

    The tamigloo protocol format specifies the following disjoint sets as the fact signature:
        \Sigma_act, \Sigma_env, \Sigma^i_state
    And the mutually disjoint sets 
        \R_env, \R_i
    for the rules.
    For b) we want to decide which objects in the tamarin theories belong to which set and make
    sure that adhere to the specified format.
-}

{- 
    Change theories parsed by the tamarin parser to theories used in the tamigloo-compiler
    by removing unused items and checking rule format to categorize rules.
-}
-- OpenTranslatedTheory is not expected to contain no sapic elements since all have been translated
changeTheory :: T.OpenTranslatedTheory -> TID.Theory
changeTheory thy = enforceConsistency $
    TID.Theory (T._thyName thy) (T._thySignature thy) (changeItems (T._thyItems thy))


-- removes items irrelevant for tamigloo-compiler
changeItems :: [T.TheoryItem T.OpenProtoRule p s] -> [TID.TheoryItem]
changeItems items = [ changeItem x | x <- items, isRelevant x]
    where
        isRelevant :: T.TheoryItem T.OpenProtoRule p s -> Bool
        isRelevant (T.RuleItem _) = True
        isRelevant (T.SapicItem _) = error "_thyItems contains SapicItems" -- should already have been translated by parser anyway
        isRelevant (T.RestrictionItem r) = checkRestrFormat r
        isRelevant _ = False
        changeItem :: T.TheoryItem T.OpenProtoRule p s -> TID.TheoryItem
        changeItem (T.RuleItem x) = TID.RuleItem (addRoleToStateRule (changeOpenProtoRule x))
        changeItem (T.TextItem x) = TID.TextItem x
        changeItem (T.RestrictionItem x) = (changeRestr x)
        changeItem _ = error "Should not be able to be here: non-exhaustive pattern match in changeItem." 


-- Format shouold be "All ts #i. ActionFact(ts) @ #i => logic(ts)"
checkRestrFormat :: Restr.Restriction -> Bool
checkRestrFormat (Restr.Restriction _name f) = checkFormFormat f && length (T.foldFrees (\x -> [x]) f) == 0
    where
        singleFact :: Form.LNFormula -> Bool
        singleFact (Form.Ato (Atom.Action _ _fact)) = True
        singleFact _ = False
        logConn :: Form.LNFormula -> Bool
        logConn (Form.Ato (Atom.EqE _ _)) = True
        logConn (Form.TF _) = True
        logConn (Form.Not form) = logConn form
        logConn (Form.Conn _ l r) = logConn l && logConn r
        logConn _ = False
        checkFormFormat :: Form.LNFormula -> Bool
        checkFormFormat (Form.Qua Form.All _hint (Form.Conn conn l r)) = 
            case conn of
                Form.Imp -> singleFact l && logConn r
                _ -> False
        checkFormFormat (Form.Qua Form.All _hint nestedF) = checkFormFormat nestedF
        checkFormFormat _ = False
        -- checks that vars used in RHS of implication are subset of vars used in LHS/Fact
        -- assumes that ForAll quanitifiers are only used to wrap the overall formula, thus the same de brujin index corresponds to same quantified var
        checkBVars :: Form.LNFormula -> Bool -- TODO add checkBVars to checkRestrFormat
        checkBVars (Form.Qua Form.All _hint (Form.Conn _conn l r)) =
            all id $ map (\e -> (elem) e (collectBVarsDups l)) (collectBVarsDups r)
        checkBVars (Form.Qua Form.All _hint nestedF) = checkBVars nestedF
        checkBVars _ = False
        collectBVarsDups :: Form.LNFormula -> [Integer] -- contains duplicates
        collectBVarsDups (Form.Ato (Atom.EqE t1 t2)) = getIntBVars t1 ++ getIntBVars t2
        collectBVarsDups (Form.Ato _) = [] -- does not conform to format
        collectBVarsDups (Form.Not form) = collectBVarsDups form
        collectBVarsDups (Form.Conn _ l r) = collectBVarsDups l ++ collectBVarsDups r
        collectBVarsDups (Form.Qua _ _ form) = collectBVarsDups form
        collectBVarsDups (Form.TF _) = []
        getIntBVars :: T.VTerm c (T.BVar T.LVar) -> [Integer]
        getIntBVars t = map (\(T.Bound i) -> i) (T.varsVTerm t)
checkRestrFormat _ = False

-- restriction change
-- should be guarded with checkRestrFormat
changeRestr :: Restr.Restriction -> TID.TheoryItem
changeRestr (Restr.Restriction name f) = TID.RestrItem name (changeLNFormToTamiForm f)

changeLNFormToTamiForm :: Form.LNFormula -> TID.RestrFormula
changeLNFormToTamiForm (Form.Ato atom) = TID.Ato (changeTypeProtoAtom atom)
changeLNFormToTamiForm (Form.TF b) = TID.Ato (TID.TF b)
changeLNFormToTamiForm (Form.Not f) = TID.Not (changeLNFormToTamiForm f)
changeLNFormToTamiForm (Form.Conn c l r) = TID.Conn c (changeLNFormToTamiForm l) (changeLNFormToTamiForm r)
changeLNFormToTamiForm (Form.Qua _ _ f) = changeLNFormToTamiForm f

changeTypeProtoAtom :: (Atom.ProtoAtom s (T.VTerm T.Name (T.BVar v))) -> TID.Atom
changeTypeProtoAtom (Atom.Action _ f) = TID.Atom (factBVarToTIDFact f)
changeTypeProtoAtom (Atom.EqE t1 t2) = TID.EqE (bVarTermToLNTerm t1) (bVarTermToLNTerm t2)
changeTypeProtoAtom _ = error "changeTypeProtoAtom called with wrong arguments."

-- change to TID.Fact
-- only used in restrictions: abuse LVar's index to represent De Brujin indices of BVar
factBVarToTIDFact :: F.Fact (T.VTerm T.Name (T.BVar v)) -> TID.Fact
factBVarToTIDFact f = changeActFact $ fmap bVarTermToLNTerm f

bVarTermToLNTerm :: (T.VTerm T.Name (T.BVar v)) -> LNTerm
bVarTermToLNTerm t = fmap (fmap bVarToLVar) t

bVarToLVar :: T.BVar v -> T.LVar
bVarToLVar (T.Bound i) = T.LVar "Bound" T.LSortNode i 
bVarToLVar (T.Free _) = error "formula should not have free variables"
-- -----------

-- checks whether a rule contains variants if not change to TRule
{- 
emptyVariantsThenChangeRule :: T.OpenProtoRule -> TID.Rule
emptyVariantsThenChangeRule r@(T.OpenProtoRule _ variants)
    | variants == [] = changeOpenProtoRule r
    | otherwise = error $ "WARNING: Rule contains variants: "++ show r

Doesn't seem necessary. Probably can just ignore variants.
-}

enforceConsistency :: TID.Theory -> TID.Theory
enforceConsistency thy@(TID.Theory name sig thyItems) =
    checkRoleInit (TID.Theory name sig (consistentItems thyItems))
    where
        cMap :: Map.Map TID.FactTag TID.FactGroup
        cMap = createConsistencyMap thy
        consistentItems :: [TID.TheoryItem] -> [TID.TheoryItem]
        consistentItems items = map
                (\i -> if TID.isRuleItem i 
                        then (TID.RuleItem $ consistentRule $ TID.getRuleFromItem i) 
                        else i) 
                items
        consistentRule :: TID.Rule -> TID.Rule
        consistentRule (TID.Rule rg n pr ac cncl) =
            TID.Rule rg n (map consistentFact pr) (map consistentFact ac) (map consistentFact cncl)
        consistentFact :: TID.Fact -> TID.Fact -- overwrites fact group according to cMap
        consistentFact (TID.Fact _ ft ts) = TID.Fact (cMap Map.! ft) ft ts

checkRoleInit :: TID.Theory -> TID.Theory
checkRoleInit thy =
    let
        initializedRoles = S.fromList $ map TID.getRoleFromSetupFact $ filter TID.isSetupFact $ concatMap TID.getFacts $ filter TID.isSetupRule $ TID.extractRules thy
        facts = concatMap TID.getFacts $ TID.extractRules thy
        usedSetupRoles = S.fromList $ map TID.getRoleFromSetupFact $ filter TID.isSetupFact facts
        usedStateRoles = S.fromList $ map TID.getRoleFromStateFact $ filter TID.isStateFact facts
        usedRoles = S.union usedSetupRoles usedStateRoles
        diff = S.difference usedRoles initializedRoles 
    in
        if null diff
        then thy
        else 
            error $ 
            "Error: The following roles are uninitialized (do not result from a setup rule):\n" ++
            (unlines $ map (\s -> "    "++s) $ S.toList diff)



createConsistencyMap :: TID.Theory -> Map.Map TID.FactTag TID.FactGroup
createConsistencyMap thy =
    let
        facts = concatMap TID.getFacts (TID.extractRules thy)
    in
        foldr getConsist Map.empty facts
    where
        getConsist :: TID.Fact -> Map.Map TID.FactTag TID.FactGroup -> Map.Map TID.FactTag TID.FactGroup
        getConsist (TID.Fact fg ft _) cMap =
            let
                mostSpec = (mostSpecificFactGroup (cMap Map.! ft) fg)
                ifRightMostSpec = fromRight (error $ errMsgConsistency ft) mostSpec
            in
                (if Map.notMember ft cMap
                then
                    Map.insert ft fg cMap
                else
                    Map.insert ft ifRightMostSpec cMap
                )
        -- returns the most specific fact group or error if fact groups cannot be resolved
        -- fact groups can only be resolved if both fact groups are in EnvGroup and at least one is in (EnvGroup Env)
        mostSpecificFactGroup :: TID.FactGroup -> TID.FactGroup -> Either String TID.FactGroup
        mostSpecificFactGroup fg1 fg2 = 
            if isEnvOtherFg fg1 || isEnvOtherFg fg2
            then
                -- case distinction on the fact group that is possibly not in (EnvGroup Env)
                let possNotEnv = (if isEnvOtherFg fg1 then fg2 else fg1) in
                case possNotEnv of
                    (TID.EnvGroup _) -> Right possNotEnv
                    _ -> Left ("fact groups not consistent " ++ show fg1 ++ show fg2)
            else
                (if fg1 == fg2 then Right fg1 else Left ("fact groups not consistent " ++ show fg1 ++ show fg2))
        errMsgConsistency :: TID.FactTag -> String
        errMsgConsistency ft = 
            let
                rules = (TID.extractRules thy)
                factWithRuleName = filter (TID.equalFactTag ft . TID.accFactTag . fst) $ concat $ zipWith zip (map TID.getFacts rules) (map (repeat . TID.accRuleName) rules) -- [(TID.Fact, String)]
                fGroupsWithRuleName = groupBy (\a b -> fst a == fst b) $ sortOn fst (map (\p -> (TID.accFactGroup $ fst p, snd p)) factWithRuleName) -- [[(TID.FactGroup, String)]]
                msgRuleNames = map (concat . map (\p -> "        " ++ snd p ++ "\n")) fGroupsWithRuleName
                msgFactGroup = map (\l -> "    The fact tag appears as " ++ (show $ fst $ head l) ++ " fact in the rules:\n" ) fGroupsWithRuleName
                msgs = foldr (++) [] (zipWith (++) msgFactGroup msgRuleNames) 
            in
                "Error: Fact groups are not consistent for fact tag: " ++ show ft ++ "\n" ++ msgs
                

isEnvIn :: TID.Fact -> Bool
isEnvIn (TID.Fact fg _ _) = isEnvInFg fg
    where
        isEnvInFg :: TID.FactGroup -> Bool
        isEnvInFg (TID.EnvGroup TID.EnvIn) = True
        isEnvInFg _ = False

isEnvOut :: TID.Fact -> Bool
isEnvOut (TID.Fact fg _ _) = isEnvOutFg fg
    where
        isEnvOutFg :: TID.FactGroup -> Bool
        isEnvOutFg (TID.EnvGroup TID.EnvOut) = True
        isEnvOutFg _ = False

isEnvOtherFg :: TID.FactGroup -> Bool
isEnvOtherFg (TID.EnvGroup TID.Env) = True
isEnvOtherFg _ = False

addRoleToStateRule :: TID.Rule -> TID.Rule
addRoleToStateRule r@(TID.Rule (TID.StateRule _) name pr act cncl)
    | checkRoles (pr ++ cncl) = TID.Rule (TID.StateRule role) name pr act cncl
    | otherwise = error $ "Rule " ++ name ++ " contains state facts of different roles:\n"++ show r
    where
        role = head $ filter (not . null) $ map extractRole (pr ++ cncl)
addRoleToStateRule r = r

-- check whether all state and setup facts in a list belong to the same role
checkRoles :: [TID.Fact] -> Bool
checkRoles fs = allSame $ filter (not . null) $ map extractRole fs

extractRole :: TID.Fact -> String
extractRole (TID.Fact _ (TID.StateFact _ s _ _) _) = s
extractRole (TID.Fact _ (TID.SetupFact _ s _ ) _) = s
extractRole _ = ""

-- checks and changes rules to be either a role's protocol(aka state) rule or an environment rule
-- Note that we change the order from pr cncl act to pr act cncl
changeOpenProtoRule :: T.OpenProtoRule -> TID.Rule
changeOpenProtoRule r@(T.OpenProtoRule (R.Rule i p c a _) _)
    | isStateRule p a c = TID.Rule (TID.StateRule "") (getNameProtoRuleEInfo i) (changeFacts "pr" p) (changeActFacts a) (changeFacts "cncl" c)
    | isEnvRule p a c = TID.Rule TID.EnvRule (getNameProtoRuleEInfo i) (changeFacts "env" p) (changeActFacts a) (changeFacts "env" c)
    | otherwise = error $ errMsgIsRule r
    where
        changeFacts :: String -> [F.LNFact] -> [TID.Fact]
        changeFacts s fs = map changeFreshPubToMsg $ case s of
            "pr" -> map changeFactPr fs
            "cncl" -> map changeFactCncl fs
            "env" -> map changeFactEnv fs
            where
                changeFactPr :: F.LNFact -> TID.Fact
                changeFactPr f@(F.Fact tag _ terms)
                    | isStateFact f = changeStateFact f
                    | isSetupFact f = changeSetupFact f
                    | otherwise = TID.Fact (TID.EnvGroup TID.EnvIn) (changeFactTag tag) terms
                changeFactCncl :: F.LNFact -> TID.Fact
                changeFactCncl f@(F.Fact tag _ terms)
                    | isStateFact f = changeStateFact f
                    | isSetupFact f = changeSetupFact f
                    | otherwise = TID.Fact (TID.EnvGroup TID.EnvOut) (changeFactTag tag) terms
                changeFactEnv :: F.LNFact -> TID.Fact    
                changeFactEnv f@(F.Fact tag _ terms)
                    | isStateFact f = changeStateFact f
                    | isSetupFact f = changeSetupFact f
                    | otherwise = TID.Fact (TID.EnvGroup TID.Env) (changeFactTag tag) terms
                changeStateFact :: F.LNFact -> TID.Fact
                changeStateFact f@(F.Fact _ _ terms) = 
                    TID.Fact TID.StateGroup (changeSFactTag "state" f) terms
                changeSetupFact :: F.LNFact -> TID.Fact
                changeSetupFact f@(F.Fact _ _ terms) = 
                    TID.Fact (TID.EnvGroup TID.EnvIn) (changeSFactTag "setup" f) terms
                -- converts Setup and State facts' facttags
                changeSFactTag :: String -> F.Fact LNTerm -> TID.FactTag
                changeSFactTag "state" fa@(F.Fact (F.ProtoFact m _s ar) _ _) = 
                    TID.StateFact m (fst (retStateFactName fa)) (snd (retStateFactName fa)) (toInteger ar)
                    where
                        retStateFactName :: F.LNFact -> (String, Integer)
                        retStateFactName fn = case (parseStateFactName fn) of {Right b -> b; _ -> ("",-1)}
                changeSFactTag "setup" fa@(F.Fact (F.ProtoFact m _s ar) _ _) = 
                    TID.SetupFact m (retSetupFactName fa) (toInteger ar)
                    where
                        retSetupFactName :: F.LNFact -> String
                        retSetupFactName fn = case (parseSetupFactName fn) of {Right b -> b; _ -> ""}
                changeSFactTag _ fa = error $ "Should be unable to be here at changeSFactTag: "++ show fa
        changeActFacts :: [F.LNFact] -> [TID.Fact]
        changeActFacts = map changeActFact

changeActFact :: F.LNFact -> TID.Fact
changeActFact (F.Fact tag _ terms) = changeFreshPubToMsg $ TID.Fact TID.ActionGroup (changeFactTag tag) terms

changeFreshPubToMsg :: TID.Fact -> TID.Fact
changeFreshPubToMsg (TID.Fact fg ft lnTerms) =
    TID.Fact fg ft (map (fmap (fmap freshPubLVarToMsg)) lnTerms)
    where
    freshPubLVarToMsg :: T.LVar -> T.LVar
    freshPubLVarToMsg (T.LVar name lsort lindex) =
        T.LVar name (newLsort lsort) lindex
    newLsort :: T.LSort -> T.LSort
    newLsort s = case s of
        T.LSortNode -> T.LSortNode
        _ -> T.LSortMsg



-- converts factTags of facts that are not Setup or State facts 
changeFactTag :: F.FactTag -> TID.FactTag
changeFactTag F.InFact = TID.InFact
changeFactTag F.OutFact = TID.OutFact
changeFactTag (F.ProtoFact m s i) = TID.ProtoFact m s (toInteger i)
changeFactTag F.FreshFact = TID.FreshFact
changeFactTag F.KUFact = TID.KUFact
changeFactTag F.KDFact = TID.KDFact
changeFactTag F.DedFact = TID.DedFact
changeFactTag F.TermFact = error "FactTag was internal TermFact. Should not happen."

-- extract the name of a rule (assume ProtoRuleEInfo is the default)
getNameProtoRuleEInfo :: R.ProtoRuleEInfo -> String
getNameProtoRuleEInfo r
    | (R.StandRule name, []) <- (R._preName r, R._preRestriction r) = name
    | R.FreshRule <- R._preName r = error $ "Unexpected FreshRule in ProtoRuleEInfo: "++ show r
    | (_:_) <- R._preRestriction r = error $ "Unexpected non-empty _preRestriction in ProtoRuleEInfo: "++ show r

errMsgIsRule :: T.OpenProtoRule -> String
errMsgIsRule (T.OpenProtoRule (R.Rule i p c a _) _) =
    "Error trying to parse (OpenProto)Rule:\n" ++
    "    The rule '" ++ getNameProtoRuleEInfo i ++ "' does not adhere to formatting assumptions.\n" ++
    "    It is not a protocol rule:\n" ++
    formatMsg (isStateRuleBoolList p a c) ++ 
    "    It is not an environment rule:\n" ++
    "        It is not a setup rule:\n" ++
    formatMsg (isSetupRuleBoolList p a c) ++
    "        It is not any other environment rule:\n" ++
    formatMsg (isEnvRuleBoolList p a c)
    where
        formatMsg :: [(Bool, String)] -> String
        formatMsg boolList = unlines $ map (\pa -> "            - " ++ snd pa ++ ": " ++ show (fst pa)) boolList



isStateRule :: [F.LNFact] -> [F.LNFact] -> [F.LNFact] -> Bool
isStateRule pr act cncl = and $ TamiHelper.fstList $ isStateRuleBoolList pr act cncl

-- list can be used for error msgs
isStateRuleBoolList :: [F.LNFact] -> [F.LNFact] -> [F.LNFact] -> [(Bool, String)]
isStateRuleBoolList pr _act cncl = 
    [ (isStateOrSetupPr pr, "premise contains a state or setup fact")
    , (isStateCncl cncl, "conclusion contains a state fact")
    ]
    where
        isStateOrSetupPr :: [F.LNFact] -> Bool
        isStateOrSetupPr p = any (\x -> isStateFact x || isSetupFact x) p
        isStateCncl :: [F.LNFact] -> Bool
        isStateCncl c = any isStateFact c

isEnvRule :: [F.LNFact] -> [F.LNFact] -> [F.LNFact] -> Bool
isEnvRule pr act cncl = 
    if (any isSetupFact cncl)
    then
        isSetupRule pr act cncl
    else
        and $ TamiHelper.fstList $ isEnvRuleBoolList pr act cncl

isEnvRuleBoolList :: [F.LNFact] -> [F.LNFact] -> [F.LNFact] -> [(Bool, String)]
isEnvRuleBoolList pr _act cncl =
    [ (all (not . isStateFact) pr, "no state facts in premise")
    , (all (not . isStateFact) cncl, "no state facts in conclusion")
    ]

isSetupRule :: [F.LNFact] -> [F.LNFact] -> [F.LNFact] -> Bool
isSetupRule pr act cncl = and $ TamiHelper.fstList $ isSetupRuleBoolList pr act cncl

isSetupRuleBoolList :: [F.LNFact] -> [F.LNFact] -> [F.LNFact] -> [(Bool, String)]
isSetupRuleBoolList pr act cncl = 
    [ (act == [], "empty action facts") 
    , (length cncl == 1, "conclusion is a single fact")
    , (all isSetupFact cncl, "the (single) conclusion is a setup fact")
    , (all (not . isStateFact) pr, "no state facts in premise") 
    , (all onlySimpleVars cncl, "no function applications as message terms in conclusion (in setup fact)") 
    ]
    where
        onlySimpleVars :: F.LNFact -> Bool
        onlySimpleVars (F.Fact _ _ terms) =
            all isLit terms

isLit :: T.VTerm c v -> Bool
isLit (viewTerm -> T.Lit _) = True
isLit _ = False

-- name of fact is of the form 'St_<role>_<step>', where <role> is an identifier, <step> is a number
isStateFact :: F.LNFact -> Bool
isStateFact f
    | (F.ProtoFact _ _ _) <- F.factTag f = isRight (parseStateFactName f)
    | otherwise = False
-- name of fact is of the form 'Setup_<role>' 
isSetupFact :: F.LNFact -> Bool
isSetupFact f
    | (F.ProtoFact _ _ _) <- F.factTag f = isRight (parseSetupFactName f)
    | otherwise = False


parseStateFactName :: F.LNFact -> Either ParseError (String, Integer)
parseStateFactName f = parseStateFactString (factName f)

parseStateFactString :: String -> Either ParseError (String, Integer)
parseStateFactString s = case Tok.parseString "" stateFactSigParser s of
    -- string contains identifier for state facts
    (Right x) -> case aux (splitRole x) of
        -- check if string also contains role and step
        (Right role, Right step) -> Right(role, step)
        (Left e, _) -> Left e
        (_, Left e) -> Left e
    -- string does not contain identifier for state fact
    (Left l) -> Left l
    where
        -- parse identifier reserved for state facts
        stateFactSigParser :: Tok.Parser String
        stateFactSigParser = (Tok.symbol "St_" *> Tok.identifier)
        aux :: (String, String) -> (Either ParseError String, Either ParseError Integer)
        aux (a, b) = (Tok.parseString "" Tok.identifier a, Tok.parseString "" (fromIntegral <$> Tok.natural) b)

{- 
    auxiliary function used for parsing state facts because <role> and <step> are separated by an underscore
    but underscores (and numbers) are also valid symbols of the <role> identifier (Tok.Parser parses everything as one).
-}
splitRole :: String -> (String, String)
splitRole s = case splitStr "_" s of
    -- for <role> concat all but the last string
    -- for <step> take the last string and "cut off" the leading underscore
    l@(_:_:_) -> (concat (init l), tail (last l)) 
    -- not enough elements to conform to <role>:_<step>:[] format 
    _ -> (s, "")


{- 
    splits string at delimiters while keeping delimiters at the left of the splitted strings
    e.g. splitStr "_" "_ab_c_" = ["", "_ab", "_c","_"]
-}
splitStr :: String -> String -> [String]
splitStr delim inp = (split . keepDelimsL . onSublist) delim inp

{-
    Setup facts are expected to be of the form 'Setup_<role>', where <role> is an identifier.
    Returns role.
-}
parseSetupFactName :: F.LNFact -> Either ParseError String
parseSetupFactName f = Tok.parseString "" setupFactSigParser (factName f)
    where
        -- parse the identifier reserved for setup facts
        setupFactSigParser :: Tok.Parser String
        setupFactSigParser = (Tok.symbol "Setup_" *> Tok.identifier)

{-
    Returns the name of a fact in the case of a protocol fact.
    For other kinds of facts returns generic name e.g. In, Fr, Out for in, out and fresh facts respectively.
-}
factName :: F.LNFact -> String
factName = (F.factTagName . F.factTag)

-- all and at least one
{-
allAndOne :: (a->Bool) -> [a] -> Bool
allAndOne _ [] = False
allAndOne f xs = all f xs
-}
allSame :: (Eq a) => [a] -> Bool
allSame xs = and $ map (uncurry (==)) $ zip xs $ tail xs

{-
intersectEq :: (a -> a -> Bool) -> [a] -> [a] -> [a]
intersectEq _f [] _ = []
intersectEq _f _ [] = []
intersectEq f (a:as) bs = 
    if (any (f a) bs)
    then a : intersectEq f as bs
    else intersectEq f as bs
-}  

