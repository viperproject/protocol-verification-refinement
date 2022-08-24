{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  TamiglooDatatypes(FactTag(..), equal_FactTag, EnvFactGroup(..), FactGroup(..),
                     Fact(..), Atom(..), RuleGroup(..), Rule(..),
                     RestrFormula(..), TheoryItem(..), Theory(..), SetOpId(..),
                     IOSTerm(..), PermType(..), PredOpId(..), IOSFormula(..),
                     accAc, accPr, isPermOpId, isPerm, predEq, accCncl,
                     getFacts, accFactTag, eqFactSig, getFactTagAr, getFactAr,
                     isEnvRule, showLSort, isFactTagPers, isFactPers,
                     isPermType, isRuleItem, varToVTerm, accPredOpId,
                     accRuleName, accTermList, addToFactAr, getActFacts,
                     getEnvFacts, getNameFactTag, getNameFact, isEnvInFact,
                     isRestrItem, isSetupFact, isSetupRule, isStateFact,
                     isStateRule, accFactGroup, accPredTerms, equalFactTag,
                     getRuleFromItem, extractRules, getVarsVTerm, isEnvOutFact,
                     extractConsts, getRestrFromItem, extractRestrs,
                     getStateFacts, updateRuleName, accPermRuleName,
                     createIOSTermVar, getVarsVTermList, replaceTermsFact,
                     createLVarFromNat, mapTermsInFormula, createLVarFromName,
                     getFactsFromFormula, getFactsFromIOSTerm,
                     getClaimsFromIOSTerm, getLNTermFromIOSTerm,
                     getRoleFromSetupFact, getRoleFromStateFact,
                     accIOSTermFactsTermList, getIOSFpredsFromFormula,
                     filterIOSFpredsFromFormulas, equal_LSort)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified ForeignImports;
import qualified HOL;
import qualified List;
import qualified GenericHelperFunctions;
import qualified Arith;

equal_Multiplicity ::
  ForeignImports.Multiplicity -> ForeignImports.Multiplicity -> Bool;
equal_Multiplicity ForeignImports.Persistent ForeignImports.Linear = False;
equal_Multiplicity ForeignImports.Linear ForeignImports.Persistent = False;
equal_Multiplicity ForeignImports.Linear ForeignImports.Linear = True;
equal_Multiplicity ForeignImports.Persistent ForeignImports.Persistent = True;

data FactTag = ProtoFact ForeignImports.Multiplicity String Integer
  | SetupFact ForeignImports.Multiplicity String Integer
  | StateFact ForeignImports.Multiplicity String Integer Integer | FreshFact
  | OutFact | InFact | KUFact | KDFact | DedFact
  deriving (Prelude.Show);

equal_FactTag :: FactTag -> FactTag -> Bool;
equal_FactTag KDFact DedFact = False;
equal_FactTag DedFact KDFact = False;
equal_FactTag KUFact DedFact = False;
equal_FactTag DedFact KUFact = False;
equal_FactTag KUFact KDFact = False;
equal_FactTag KDFact KUFact = False;
equal_FactTag InFact DedFact = False;
equal_FactTag DedFact InFact = False;
equal_FactTag InFact KDFact = False;
equal_FactTag KDFact InFact = False;
equal_FactTag InFact KUFact = False;
equal_FactTag KUFact InFact = False;
equal_FactTag OutFact DedFact = False;
equal_FactTag DedFact OutFact = False;
equal_FactTag OutFact KDFact = False;
equal_FactTag KDFact OutFact = False;
equal_FactTag OutFact KUFact = False;
equal_FactTag KUFact OutFact = False;
equal_FactTag OutFact InFact = False;
equal_FactTag InFact OutFact = False;
equal_FactTag FreshFact DedFact = False;
equal_FactTag DedFact FreshFact = False;
equal_FactTag FreshFact KDFact = False;
equal_FactTag KDFact FreshFact = False;
equal_FactTag FreshFact KUFact = False;
equal_FactTag KUFact FreshFact = False;
equal_FactTag FreshFact InFact = False;
equal_FactTag InFact FreshFact = False;
equal_FactTag FreshFact OutFact = False;
equal_FactTag OutFact FreshFact = False;
equal_FactTag (StateFact x31 x32 x33 x34) DedFact = False;
equal_FactTag DedFact (StateFact x31 x32 x33 x34) = False;
equal_FactTag (StateFact x31 x32 x33 x34) KDFact = False;
equal_FactTag KDFact (StateFact x31 x32 x33 x34) = False;
equal_FactTag (StateFact x31 x32 x33 x34) KUFact = False;
equal_FactTag KUFact (StateFact x31 x32 x33 x34) = False;
equal_FactTag (StateFact x31 x32 x33 x34) InFact = False;
equal_FactTag InFact (StateFact x31 x32 x33 x34) = False;
equal_FactTag (StateFact x31 x32 x33 x34) OutFact = False;
equal_FactTag OutFact (StateFact x31 x32 x33 x34) = False;
equal_FactTag (StateFact x31 x32 x33 x34) FreshFact = False;
equal_FactTag FreshFact (StateFact x31 x32 x33 x34) = False;
equal_FactTag (SetupFact x21 x22 x23) DedFact = False;
equal_FactTag DedFact (SetupFact x21 x22 x23) = False;
equal_FactTag (SetupFact x21 x22 x23) KDFact = False;
equal_FactTag KDFact (SetupFact x21 x22 x23) = False;
equal_FactTag (SetupFact x21 x22 x23) KUFact = False;
equal_FactTag KUFact (SetupFact x21 x22 x23) = False;
equal_FactTag (SetupFact x21 x22 x23) InFact = False;
equal_FactTag InFact (SetupFact x21 x22 x23) = False;
equal_FactTag (SetupFact x21 x22 x23) OutFact = False;
equal_FactTag OutFact (SetupFact x21 x22 x23) = False;
equal_FactTag (SetupFact x21 x22 x23) FreshFact = False;
equal_FactTag FreshFact (SetupFact x21 x22 x23) = False;
equal_FactTag (SetupFact x21 x22 x23) (StateFact x31 x32 x33 x34) = False;
equal_FactTag (StateFact x31 x32 x33 x34) (SetupFact x21 x22 x23) = False;
equal_FactTag (ProtoFact x11 x12 x13) DedFact = False;
equal_FactTag DedFact (ProtoFact x11 x12 x13) = False;
equal_FactTag (ProtoFact x11 x12 x13) KDFact = False;
equal_FactTag KDFact (ProtoFact x11 x12 x13) = False;
equal_FactTag (ProtoFact x11 x12 x13) KUFact = False;
equal_FactTag KUFact (ProtoFact x11 x12 x13) = False;
equal_FactTag (ProtoFact x11 x12 x13) InFact = False;
equal_FactTag InFact (ProtoFact x11 x12 x13) = False;
equal_FactTag (ProtoFact x11 x12 x13) OutFact = False;
equal_FactTag OutFact (ProtoFact x11 x12 x13) = False;
equal_FactTag (ProtoFact x11 x12 x13) FreshFact = False;
equal_FactTag FreshFact (ProtoFact x11 x12 x13) = False;
equal_FactTag (ProtoFact x11 x12 x13) (StateFact x31 x32 x33 x34) = False;
equal_FactTag (StateFact x31 x32 x33 x34) (ProtoFact x11 x12 x13) = False;
equal_FactTag (ProtoFact x11 x12 x13) (SetupFact x21 x22 x23) = False;
equal_FactTag (SetupFact x21 x22 x23) (ProtoFact x11 x12 x13) = False;
equal_FactTag (StateFact x31 x32 x33 x34) (StateFact y31 y32 y33 y34) =
  equal_Multiplicity x31 y31 && x32 == y32 && x33 == y33 && x34 == y34;
equal_FactTag (SetupFact x21 x22 x23) (SetupFact y21 y22 y23) =
  equal_Multiplicity x21 y21 && x22 == y22 && x23 == y23;
equal_FactTag (ProtoFact x11 x12 x13) (ProtoFact y11 y12 y13) =
  equal_Multiplicity x11 y11 && x12 == y12 && x13 == y13;
equal_FactTag DedFact DedFact = True;
equal_FactTag KDFact KDFact = True;
equal_FactTag KUFact KUFact = True;
equal_FactTag InFact InFact = True;
equal_FactTag OutFact OutFact = True;
equal_FactTag FreshFact FreshFact = True;

instance Eq FactTag where {
  a == b = equal_FactTag a b;
};

data EnvFactGroup = EnvIn | EnvOut | Env deriving (Prelude.Show);

data FactGroup = EnvGroup EnvFactGroup | ActionGroup | StateGroup
  deriving (Prelude.Show);

data Fact =
  Fact FactGroup FactTag
    [ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar)]
  deriving (Prelude.Show);

data Atom = Atom Fact
  | EqE (ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar))
      (ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar))
  | TF Bool deriving (Prelude.Show);

data RuleGroup = EnvRule | StateRule String
  deriving (Prelude.Show);

data Rule = Rule RuleGroup String [Fact] [Fact] [Fact]
  deriving (Prelude.Show);

data RestrFormula = Ato Atom | Not RestrFormula
  | Conn ForeignImports.Connective RestrFormula RestrFormula
  | REX (ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar))
      RestrFormula
  deriving (Prelude.Show);

data TheoryItem = RuleItem Rule | TextItem (String, String)
  | RestrItem String RestrFormula deriving (Prelude.Show);

data Theory = Theory String ForeignImports.SignaturePure [TheoryItem]
  deriving (Prelude.Show);

data SetOpId = MDiff | MUnion | UpdateSt deriving (Prelude.Show);

data IOSTerm =
  IOSTermVar
    (ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar))
  | IOSTermFacts [Fact] | IOSTermClaims [Fact] | IOSTermSetOp SetOpId [IOSTerm]
  deriving (Prelude.Show);

data PermType = Internal_R | In_RF | Out_RG
  deriving (Prelude.Show);

data PredOpId = Equal | MIn | Perm PermType String | Token | Pred String
  deriving (Prelude.Show);

data IOSFormula = IOSFpred PredOpId [IOSTerm] | IOSFRestr RestrFormula
  | IOSFand IOSFormula IOSFormula | IOSFimpl IOSFormula IOSFormula
  | IOSFsepConj [IOSFormula] | IOSFex IOSTerm IOSFormula
  | IOSFfa IOSTerm IOSFormula deriving (Prelude.Show);

accAc :: Rule -> [Fact];
accAc (Rule uu uv uw ac ux) = ac;

accPr :: Rule -> [Fact];
accPr (Rule uu uv pr uw ux) = pr;

isPermOpId :: PredOpId -> Bool;
isPermOpId pOp = (case pOp of {
                   Equal -> False;
                   MIn -> False;
                   Perm _ _ -> True;
                   Token -> False;
                   Pred _ -> False;
                 });

isPerm :: IOSFormula -> Bool;
isPerm f = (case f of {
             IOSFpred op _ -> isPermOpId op;
             IOSFRestr _ -> False;
             IOSFand _ _ -> False;
             IOSFimpl _ _ -> False;
             IOSFsepConj _ -> False;
             IOSFex _ _ -> False;
             IOSFfa _ _ -> False;
           });

predEq :: IOSTerm -> IOSTerm -> IOSFormula;
predEq a b = IOSFpred Equal [a, b];

accCncl :: Rule -> [Fact];
accCncl (Rule uu uv uw ux cncl) = cncl;

getFacts :: Rule -> [Fact];
getFacts (Rule uu uv pr ac cncl) = pr ++ ac ++ cncl;

accFactTag :: Fact -> FactTag;
accFactTag (Fact uu ft uv) = ft;

eqFactSig :: Fact -> Fact -> Bool;
eqFactSig f1 f2 = equal_FactTag (accFactTag f1) (accFactTag f2);

getFactTagAr :: FactTag -> Arith.Nat;
getFactTagAr ft = (case ft of {
                    ProtoFact _ _ a -> Arith.nat_of_integer a;
                    SetupFact _ _ a -> Arith.nat_of_integer a;
                    StateFact _ _ _ a -> Arith.nat_of_integer a;
                    FreshFact -> Arith.one_nat;
                    OutFact -> Arith.one_nat;
                    InFact -> Arith.one_nat;
                    KUFact -> Arith.one_nat;
                    KDFact -> Arith.one_nat;
                    DedFact -> Arith.one_nat;
                  });

getFactAr :: Fact -> Arith.Nat;
getFactAr f = getFactTagAr (accFactTag f);

getVarLit :: forall a b. ForeignImports.Lit a b -> Maybe b;
getVarLit (ForeignImports.Var v) = Just v;
getVarLit (ForeignImports.Con v) = Nothing;

isActFact :: Fact -> Bool;
isActFact (Fact ActionGroup uu uv) = True;
isActFact (Fact (EnvGroup vc) va vb) = False;
isActFact (Fact StateGroup va vb) = False;

isEnvFact :: Fact -> Bool;
isEnvFact (Fact (EnvGroup uu) uv uw) = True;
isEnvFact (Fact ActionGroup va vb) = False;
isEnvFact (Fact StateGroup va vb) = False;

isEnvRule :: Rule -> Bool;
isEnvRule (Rule EnvRule uu uv uw ux) = True;
isEnvRule (Rule (StateRule ve) va vb vc vd) = False;

showLSort :: ForeignImports.LSort -> String;
showLSort lsort = (case lsort of {
                    ForeignImports.LSortPub -> "pub";
                    ForeignImports.LSortFresh -> "fr";
                    ForeignImports.LSortMsg -> "msg";
                    ForeignImports.LSortNode -> "node";
                  });

isPersistent :: ForeignImports.Multiplicity -> Bool;
isPersistent ForeignImports.Persistent = True;
isPersistent ForeignImports.Linear = False;

isFactTagPers :: FactTag -> Bool;
isFactTagPers ft = (case ft of {
                     ProtoFact m _ _ -> isPersistent m;
                     SetupFact m _ _ -> isPersistent m;
                     StateFact m _ _ _ -> isPersistent m;
                     FreshFact -> False;
                     OutFact -> False;
                     InFact -> False;
                     KUFact -> True;
                     KDFact -> True;
                     DedFact -> False;
                   });

isFactPers :: Fact -> Bool;
isFactPers f = isFactTagPers (accFactTag f);

equal_PermType :: PermType -> PermType -> Bool;
equal_PermType In_RF Out_RG = False;
equal_PermType Out_RG In_RF = False;
equal_PermType Internal_R Out_RG = False;
equal_PermType Out_RG Internal_R = False;
equal_PermType Internal_R In_RF = False;
equal_PermType In_RF Internal_R = False;
equal_PermType Out_RG Out_RG = True;
equal_PermType In_RF In_RF = True;
equal_PermType Internal_R Internal_R = True;

isPermType :: PermType -> PredOpId -> Bool;
isPermType typea pOp = (case pOp of {
                         Equal -> False;
                         MIn -> False;
                         Perm t _ -> equal_PermType t typea;
                         Token -> False;
                         Pred _ -> False;
                       });

isRuleItem :: TheoryItem -> Bool;
isRuleItem (RuleItem uu) = True;
isRuleItem (TextItem v) = False;
isRuleItem (RestrItem v va) = False;

varToVTerm ::
  forall a. a -> ForeignImports.Term (ForeignImports.Lit ForeignImports.Name a);
varToVTerm v = ForeignImports.LIT (ForeignImports.Var v);

accPredOpId :: IOSFormula -> PredOpId;
accPredOpId f = (case f of {
                  IOSFpred pOp _ -> pOp;
                });

accRuleName :: Rule -> String;
accRuleName (Rule uu rName uv uw ux) = rName;

accTermList ::
  Fact ->
    [ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar)];
accTermList (Fact uu uv termList) = termList;

accThyItems :: Theory -> [TheoryItem];
accThyItems (Theory uu uv a) = a;

addToFactAr :: Integer -> Fact -> Fact;
addToFactAr a (Fact fg ft ts) =
  (case ft of {
    ProtoFact mult name ar -> Fact fg (ProtoFact mult name (ar + a)) ts;
    SetupFact mult role ar -> Fact fg (SetupFact mult role (ar + a)) ts;
    StateFact mult role step ar ->
      Fact fg (StateFact mult role step (ar + a)) ts;
  });

getActFacts :: Rule -> [Fact];
getActFacts r = filter isActFact (getFacts r);

getConstLit :: forall a b. ForeignImports.Lit a b -> Maybe a;
getConstLit (ForeignImports.Con c) = Just c;
getConstLit (ForeignImports.Var v) = Nothing;

getEnvFacts :: Rule -> [Fact];
getEnvFacts r = filter isEnvFact (getFacts r);

getNameFactTag :: FactTag -> String;
getNameFactTag ft =
  (case ft of {
    ProtoFact _ name _ -> name;
    SetupFact _ role _ -> GenericHelperFunctions.prependToString "Setup" role;
    StateFact _ role step _ ->
      GenericHelperFunctions.prependToString
        (GenericHelperFunctions.prependToString "St" role)
        (GenericHelperFunctions.stringOfInteger step);
    FreshFact -> "FrFact";
    OutFact -> "OutFact";
    InFact -> "InFact";
    KUFact -> "K";
    KDFact -> "K";
    DedFact -> "K";
  });

getNameFact :: Fact -> String;
getNameFact f = getNameFactTag (accFactTag f);

isEnvInFact :: Fact -> Bool;
isEnvInFact (Fact (EnvGroup EnvIn) uu uv) = True;
isEnvInFact (Fact (EnvGroup EnvOut) va vb) = False;
isEnvInFact (Fact (EnvGroup Env) va vb) = False;
isEnvInFact (Fact ActionGroup va vb) = False;
isEnvInFact (Fact StateGroup va vb) = False;

isRestrItem :: TheoryItem -> Bool;
isRestrItem (RestrItem uu uv) = True;
isRestrItem (RuleItem v) = False;
isRestrItem (TextItem v) = False;

isSetupFact :: Fact -> Bool;
isSetupFact (Fact uu (SetupFact uv uw ux) uy) = True;
isSetupFact (Fact v (ProtoFact vc vd ve) vb) = False;
isSetupFact (Fact v (StateFact vc vd ve vf) vb) = False;
isSetupFact (Fact v FreshFact vb) = False;
isSetupFact (Fact v OutFact vb) = False;
isSetupFact (Fact v InFact vb) = False;
isSetupFact (Fact v KUFact vb) = False;
isSetupFact (Fact v KDFact vb) = False;
isSetupFact (Fact v DedFact vb) = False;

isSetupRule :: Rule -> Bool;
isSetupRule (Rule uu uv uw ux cncl) =
  GenericHelperFunctions.anya isSetupFact cncl;

isStateFact :: Fact -> Bool;
isStateFact (Fact StateGroup uu uv) = True;
isStateFact (Fact (EnvGroup vc) va vb) = False;
isStateFact (Fact ActionGroup va vb) = False;

isStateRule :: Rule -> Bool;
isStateRule (Rule (StateRule uu) uv uw ux uy) = True;
isStateRule (Rule EnvRule va vb vc vd) = False;

accFactGroup :: Fact -> FactGroup;
accFactGroup (Fact fg uu uv) = fg;

accPredTerms :: IOSFormula -> [IOSTerm];
accPredTerms f = (case f of {
                   IOSFpred _ ts -> ts;
                 });

equalFactTag :: FactTag -> FactTag -> Bool;
equalFactTag f1 f2 = equal_FactTag f1 f2;

getRuleFromItem :: TheoryItem -> Rule;
getRuleFromItem (RuleItem r) = r;
getRuleFromItem (TextItem v) = error "undefined";
getRuleFromItem (RestrItem v va) = error "undefined";

extractRules :: Theory -> [Rule];
extractRules thy =
  List.map_filter
    (\ x -> (if isRuleItem x then Just (getRuleFromItem x) else Nothing))
    (accThyItems thy);

collectLitsVTerm ::
  forall a b.
    ForeignImports.Term (ForeignImports.Lit a b) -> [ForeignImports.Lit a b];
collectLitsVTerm t = (case t of {
                       ForeignImports.LIT lit -> [lit];
                       ForeignImports.FAPP _ a -> concatMap collectLitsVTerm a;
                     });

getVarsVTerm ::
  forall a b. (Eq b) => ForeignImports.Term (ForeignImports.Lit a b) -> [b];
getVarsVTerm vt =
  let {
    a = map getVarLit (collectLitsVTerm vt);
  } in (GenericHelperFunctions.nub . GenericHelperFunctions.collectThe) a;

isEnvOutFact :: Fact -> Bool;
isEnvOutFact (Fact (EnvGroup EnvOut) uu uv) = True;
isEnvOutFact (Fact (EnvGroup EnvIn) va vb) = False;
isEnvOutFact (Fact (EnvGroup Env) va vb) = False;
isEnvOutFact (Fact ActionGroup va vb) = False;
isEnvOutFact (Fact StateGroup va vb) = False;

getConstsVTermWithDuplicates ::
  forall a b. ForeignImports.Term (ForeignImports.Lit a b) -> [a];
getConstsVTermWithDuplicates vt = let {
                                    a = map getConstLit (collectLitsVTerm vt);
                                  } in GenericHelperFunctions.collectThe a;

extractConsts :: Theory -> [ForeignImports.Name];
extractConsts thy = let {
                      facts = concatMap getFacts (extractRules thy);
                      a = concatMap accTermList facts;
                    } in concatMap getConstsVTermWithDuplicates a;

getRestrFromItem :: TheoryItem -> RestrFormula;
getRestrFromItem (RestrItem n r) = r;
getRestrFromItem (RuleItem v) = error "undefined";
getRestrFromItem (TextItem v) = error "undefined";

extractRestrs :: Theory -> [RestrFormula];
extractRestrs thy =
  List.map_filter
    (\ x -> (if isRestrItem x then Just (getRestrFromItem x) else Nothing))
    (accThyItems thy);

getStateFacts :: Rule -> [Fact];
getStateFacts r = filter isStateFact (getFacts r);

mapTermInPred ::
  (Integer -> IOSTerm -> IOSTerm) -> Integer -> IOSFormula -> IOSFormula;
mapTermInPred f i (IOSFpred op ts) = IOSFpred op (map (f i) ts);

updateRuleName :: String -> Rule -> Rule;
updateRuleName newName (Rule rg uu pr ac cncl) = Rule rg newName pr ac cncl;

accPermRuleName :: PredOpId -> String;
accPermRuleName pOp = (case pOp of {
                        Perm _ ruleName -> ruleName;
                      });

createIOSTermVar :: ForeignImports.LVar -> IOSTerm;
createIOSTermVar v = IOSTermVar (varToVTerm v);

getVarsVTermList ::
  forall a b. (Eq b) => [ForeignImports.Term (ForeignImports.Lit a b)] -> [b];
getVarsVTermList ls = GenericHelperFunctions.nub (concatMap getVarsVTerm ls);

replaceTermsFact ::
  [ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar)] ->
    Fact -> Fact;
replaceTermsFact newTs (Fact fg ft ts) = Fact fg ft newTs;

createLVarFromNat :: Arith.Nat -> ForeignImports.LVar;
createLVarFromNat n =
  ForeignImports.LVar "var" ForeignImports.LSortMsg (Arith.integer_of_nat n);

changePredInFormula ::
  (Integer -> IOSFormula -> IOSFormula) -> Integer -> IOSFormula -> IOSFormula;
changePredInFormula f i form =
  (case form of {
    IOSFpred _ _ -> f i form;
    IOSFRestr a -> IOSFRestr a;
    IOSFand a b ->
      IOSFand (changePredInFormula f i a) (changePredInFormula f i b);
    IOSFimpl a b ->
      IOSFimpl (changePredInFormula f i a) (changePredInFormula f i b);
    IOSFsepConj ls -> IOSFsepConj (map (changePredInFormula f i) ls);
    IOSFex t a -> IOSFex t (changePredInFormula f (i + (1 :: Integer)) a);
    IOSFfa t a -> IOSFfa t (changePredInFormula f (i + (1 :: Integer)) a);
  });

mapTermsInFormula ::
  (Integer -> IOSTerm -> IOSTerm) -> IOSFormula -> IOSFormula;
mapTermsInFormula f form =
  changePredInFormula (mapTermInPred f) (0 :: Integer) form;

createLVarFromName :: String -> ForeignImports.LVar;
createLVarFromName name =
  ForeignImports.LVar name ForeignImports.LSortMsg (0 :: Integer);

getFactsFromFormula :: (IOSTerm -> [Fact]) -> IOSFormula -> [Fact];
getFactsFromFormula collectFun f =
  (case f of {
    IOSFpred _ a -> concatMap collectFun a;
    IOSFRestr _ -> [];
    IOSFand a b ->
      getFactsFromFormula collectFun a ++ getFactsFromFormula collectFun b;
    IOSFimpl a b ->
      getFactsFromFormula collectFun a ++ getFactsFromFormula collectFun b;
    IOSFsepConj a -> concatMap (getFactsFromFormula collectFun) a;
    IOSFex v inF -> collectFun v ++ getFactsFromFormula collectFun inF;
    IOSFfa v inF -> collectFun v ++ getFactsFromFormula collectFun inF;
  });

getFactsFromIOSTerm :: IOSTerm -> [Fact];
getFactsFromIOSTerm (IOSTermFacts fs) = fs;
getFactsFromIOSTerm (IOSTermVar v) = [];
getFactsFromIOSTerm (IOSTermClaims v) = [];
getFactsFromIOSTerm (IOSTermSetOp v va) = [];

getClaimsFromIOSTerm :: IOSTerm -> [Fact];
getClaimsFromIOSTerm (IOSTermClaims fs) = fs;
getClaimsFromIOSTerm (IOSTermVar v) = [];
getClaimsFromIOSTerm (IOSTermFacts v) = [];
getClaimsFromIOSTerm (IOSTermSetOp v va) = [];

getLNTermFromIOSTerm ::
  IOSTerm ->
    ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar);
getLNTermFromIOSTerm iosT = (case iosT of {
                              IOSTermVar lnTerm -> lnTerm;
                            });

getRoleFromSetupFact :: Fact -> String;
getRoleFromSetupFact (Fact uu (SetupFact uv role uw) ux) = role;
getRoleFromSetupFact (Fact v (ProtoFact vc vd ve) vb) = error "undefined";
getRoleFromSetupFact (Fact v (StateFact vc vd ve vf) vb) = error "undefined";
getRoleFromSetupFact (Fact v FreshFact vb) = error "undefined";
getRoleFromSetupFact (Fact v OutFact vb) = error "undefined";
getRoleFromSetupFact (Fact v InFact vb) = error "undefined";
getRoleFromSetupFact (Fact v KUFact vb) = error "undefined";
getRoleFromSetupFact (Fact v KDFact vb) = error "undefined";
getRoleFromSetupFact (Fact v DedFact vb) = error "undefined";

getRoleFromStateFact :: Fact -> String;
getRoleFromStateFact (Fact uu (StateFact uv role uw ux) uy) = role;
getRoleFromStateFact (Fact v (ProtoFact vc vd ve) vb) = error "undefined";
getRoleFromStateFact (Fact v (SetupFact vc vd ve) vb) = error "undefined";
getRoleFromStateFact (Fact v FreshFact vb) = error "undefined";
getRoleFromStateFact (Fact v OutFact vb) = error "undefined";
getRoleFromStateFact (Fact v InFact vb) = error "undefined";
getRoleFromStateFact (Fact v KUFact vb) = error "undefined";
getRoleFromStateFact (Fact v KDFact vb) = error "undefined";
getRoleFromStateFact (Fact v DedFact vb) = error "undefined";

accIOSTermFactsTermList ::
  IOSTerm ->
    [ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar)];
accIOSTermFactsTermList (IOSTermFacts fs) = concatMap accTermList fs;
accIOSTermFactsTermList (IOSTermClaims fs) = concatMap accTermList fs;
accIOSTermFactsTermList (IOSTermVar v) = error "undefined";
accIOSTermFactsTermList (IOSTermSetOp v va) = error "undefined";

getIOSFpredsFromFormula :: IOSFormula -> [IOSFormula];
getIOSFpredsFromFormula f =
  (case f of {
    IOSFpred predOp ts -> [IOSFpred predOp ts];
    IOSFRestr _ -> [];
    IOSFand a b -> getIOSFpredsFromFormula a ++ getIOSFpredsFromFormula b;
    IOSFimpl a b -> getIOSFpredsFromFormula a ++ getIOSFpredsFromFormula b;
    IOSFsepConj a -> concatMap getIOSFpredsFromFormula a;
    IOSFex _ a -> getIOSFpredsFromFormula a;
    IOSFfa _ a -> getIOSFpredsFromFormula a;
  });

filterIOSFpredsFromFormulas ::
  (IOSFormula -> Bool) -> [IOSFormula] -> [IOSFormula];
filterIOSFpredsFromFormulas filterFun fs =
  filter filterFun (concatMap getIOSFpredsFromFormula fs);

equal_LSort :: ForeignImports.LSort -> ForeignImports.LSort -> Bool;
equal_LSort ForeignImports.LSortMsg ForeignImports.LSortNode = False;
equal_LSort ForeignImports.LSortNode ForeignImports.LSortMsg = False;
equal_LSort ForeignImports.LSortFresh ForeignImports.LSortNode = False;
equal_LSort ForeignImports.LSortNode ForeignImports.LSortFresh = False;
equal_LSort ForeignImports.LSortFresh ForeignImports.LSortMsg = False;
equal_LSort ForeignImports.LSortMsg ForeignImports.LSortFresh = False;
equal_LSort ForeignImports.LSortPub ForeignImports.LSortNode = False;
equal_LSort ForeignImports.LSortNode ForeignImports.LSortPub = False;
equal_LSort ForeignImports.LSortPub ForeignImports.LSortMsg = False;
equal_LSort ForeignImports.LSortMsg ForeignImports.LSortPub = False;
equal_LSort ForeignImports.LSortPub ForeignImports.LSortFresh = False;
equal_LSort ForeignImports.LSortFresh ForeignImports.LSortPub = False;
equal_LSort ForeignImports.LSortNode ForeignImports.LSortNode = True;
equal_LSort ForeignImports.LSortMsg ForeignImports.LSortMsg = True;
equal_LSort ForeignImports.LSortFresh ForeignImports.LSortFresh = True;
equal_LSort ForeignImports.LSortPub ForeignImports.LSortPub = True;

}
