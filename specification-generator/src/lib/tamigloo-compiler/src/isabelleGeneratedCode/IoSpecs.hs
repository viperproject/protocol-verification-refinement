{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  IoSpecs(var_rid, termVar_rid, var_s, termVar_s, var_p, termVar_p, var_ap,
           var_lp, var_pp, var_rp, termVar_rp, termVar_pp, termVar_lp,
           termVar_ap, makeNameLVar, extractIOSpec, getAbsPWithDef,
           getAbsPsiWithDef, getAbsPhisWithDef, createIOSTermVarFromName)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified ForeignImports;
import qualified Decomposition;
import qualified Restrictions;
import qualified Arith;
import qualified List;
import qualified GenericHelperFunctions;
import qualified HOL;
import qualified TamiglooDatatypes;

permR ::
  TamiglooDatatypes.Rule ->
    [TamiglooDatatypes.IOSTerm] -> TamiglooDatatypes.IOSFormula;
permR rule ts =
  let {
    ruleName =
      GenericHelperFunctions.prependToString "e"
        (TamiglooDatatypes.accRuleName rule);
  } in TamiglooDatatypes.IOSFpred
         (TamiglooDatatypes.Perm TamiglooDatatypes.Internal_R ruleName) ts;

predM ::
  TamiglooDatatypes.IOSTerm ->
    TamiglooDatatypes.IOSTerm -> TamiglooDatatypes.IOSFormula;
predM lp state =
  TamiglooDatatypes.IOSFpred (TamiglooDatatypes.Pred "M") [lp, state];

var_rid :: ForeignImports.LVar;
var_rid = TamiglooDatatypes.createLVarFromName "tami_rid";

termVar_rid :: TamiglooDatatypes.IOSTerm;
termVar_rid = TamiglooDatatypes.createIOSTermVar var_rid;

var_s :: ForeignImports.LVar;
var_s = TamiglooDatatypes.createLVarFromName "tami_s";

termVar_s :: TamiglooDatatypes.IOSTerm;
termVar_s = TamiglooDatatypes.createIOSTermVar var_s;

var_p :: ForeignImports.LVar;
var_p = TamiglooDatatypes.createLVarFromName "tami_p";

termVar_p :: TamiglooDatatypes.IOSTerm;
termVar_p = TamiglooDatatypes.createIOSTermVar var_p;

absPredPhiRG ::
  String -> Arith.Nat -> TamiglooDatatypes.Rule -> TamiglooDatatypes.IOSFormula;
absPredPhiRG role index rule =
  let {
    name =
      GenericHelperFunctions.prependToString "phiRG"
        (GenericHelperFunctions.prependToString role
          (GenericHelperFunctions.stringOfNat index));
  } in TamiglooDatatypes.IOSFpred (TamiglooDatatypes.Pred name)
         [termVar_p, termVar_rid, termVar_s];

absPredPhiRF ::
  String -> Arith.Nat -> TamiglooDatatypes.Rule -> TamiglooDatatypes.IOSFormula;
absPredPhiRF role index rule =
  let {
    name =
      GenericHelperFunctions.prependToString "phiRF"
        (GenericHelperFunctions.prependToString role
          (GenericHelperFunctions.stringOfNat index));
  } in TamiglooDatatypes.IOSFpred (TamiglooDatatypes.Pred name)
         [termVar_p, termVar_rid, termVar_s];

absPredPhiR ::
  String -> Arith.Nat -> TamiglooDatatypes.Rule -> TamiglooDatatypes.IOSFormula;
absPredPhiR role index rule =
  let {
    name =
      GenericHelperFunctions.prependToString "phiR"
        (GenericHelperFunctions.prependToString role
          (GenericHelperFunctions.stringOfNat index));
  } in TamiglooDatatypes.IOSFpred (TamiglooDatatypes.Pred name)
         [termVar_p, termVar_rid, termVar_s];

collectAbsPhi ::
  String ->
    [TamiglooDatatypes.Rule] ->
      [TamiglooDatatypes.Rule] ->
        [TamiglooDatatypes.Rule] ->
          [(String, (TamiglooDatatypes.Rule, TamiglooDatatypes.IOSFormula))];
collectAbsPhi role rProto rIoIn rIoOut =
  let {
    enum_rProto = GenericHelperFunctions.enum Arith.zero_nat rProto;
    enum_rIoOut = GenericHelperFunctions.enum (List.size_list rProto) rIoOut;
    enum_rIoIn =
      GenericHelperFunctions.enum
        (Arith.plus_nat (List.size_list rProto) (List.size_list rIoOut)) rIoIn;
    roleRulePhiR = (\ p -> (role, (snd p, absPredPhiR role (fst p) (snd p))));
    roleRulePhiRG = (\ p -> (role, (snd p, absPredPhiRG role (fst p) (snd p))));
    roleRulePhiRF = (\ p -> (role, (snd p, absPredPhiRF role (fst p) (snd p))));
  } in concat
         [map roleRulePhiR enum_rProto, map roleRulePhiRG enum_rIoOut,
           map roleRulePhiRF enum_rIoIn];

predP ::
  String ->
    [TamiglooDatatypes.Rule] ->
      [TamiglooDatatypes.Rule] ->
        [TamiglooDatatypes.Rule] -> TamiglooDatatypes.IOSFormula;
predP role rProto rIoIn rIoOut =
  let {
    absPhiTri = collectAbsPhi role rProto rIoIn rIoOut;
    a = map (\ t -> snd (snd t)) absPhiTri;
  } in TamiglooDatatypes.IOSFsepConj a;

permRF ::
  TamiglooDatatypes.Rule ->
    [TamiglooDatatypes.IOSTerm] -> TamiglooDatatypes.IOSFormula;
permRF rule ts =
  let {
    slName =
      GenericHelperFunctions.prependToString "e"
        (GenericHelperFunctions.splitAndGetSnd
          (TamiglooDatatypes.getNameFact
            (List.hd (TamiglooDatatypes.accAc rule))));
  } in TamiglooDatatypes.IOSFpred
         (TamiglooDatatypes.Perm TamiglooDatatypes.In_RF slName) ts;

permRG ::
  TamiglooDatatypes.Rule ->
    [TamiglooDatatypes.IOSTerm] -> TamiglooDatatypes.IOSFormula;
permRG rule ts =
  let {
    slName =
      GenericHelperFunctions.prependToString "e"
        (GenericHelperFunctions.splitAndGetSnd
          (TamiglooDatatypes.getNameFact
            (List.hd (TamiglooDatatypes.accAc rule))));
  } in TamiglooDatatypes.IOSFpred
         (TamiglooDatatypes.Perm TamiglooDatatypes.Out_RG slName) ts;

tokenP :: TamiglooDatatypes.IOSFormula;
tokenP = TamiglooDatatypes.IOSFpred TamiglooDatatypes.Token [termVar_p];

var_ap :: ForeignImports.LVar;
var_ap = TamiglooDatatypes.createLVarFromName "tami_ap";

var_lp :: ForeignImports.LVar;
var_lp = TamiglooDatatypes.createLVarFromName "tami_lp";

var_pp :: ForeignImports.LVar;
var_pp = TamiglooDatatypes.createLVarFromName "tami_pp";

var_rp :: ForeignImports.LVar;
var_rp = TamiglooDatatypes.createLVarFromName "tami_rp";

absPredP ::
  String -> [TamiglooDatatypes.IOSTerm] -> TamiglooDatatypes.IOSFormula;
absPredP role ts =
  TamiglooDatatypes.IOSFpred
    (TamiglooDatatypes.Pred (GenericHelperFunctions.prependToString "P" role))
    ts;

predPsi ::
  String -> (TamiglooDatatypes.IOSFormula, TamiglooDatatypes.IOSFormula);
predPsi role =
  let {
    name = GenericHelperFunctions.prependToString "psi" role;
    absPredPsi =
      TamiglooDatatypes.IOSFpred (TamiglooDatatypes.Pred name) [termVar_rid];
  } in (absPredPsi,
         TamiglooDatatypes.IOSFex termVar_p
           (TamiglooDatatypes.IOSFsepConj
             [tokenP,
               absPredP role
                 [termVar_p, termVar_rid, TamiglooDatatypes.IOSTermFacts []]]));

wrapInForAll ::
  [TamiglooDatatypes.IOSTerm] ->
    TamiglooDatatypes.IOSFormula -> TamiglooDatatypes.IOSFormula;
wrapInForAll [] f = f;
wrapInForAll (t : ts) f = TamiglooDatatypes.IOSFfa t (wrapInForAll ts f);

termVar_rp :: TamiglooDatatypes.IOSTerm;
termVar_rp = TamiglooDatatypes.createIOSTermVar var_rp;

termVar_pp :: TamiglooDatatypes.IOSTerm;
termVar_pp = TamiglooDatatypes.createIOSTermVar var_pp;

termVar_lp :: TamiglooDatatypes.IOSTerm;
termVar_lp = TamiglooDatatypes.createIOSTermVar var_lp;

termVar_ap :: TamiglooDatatypes.IOSTerm;
termVar_ap = TamiglooDatatypes.createIOSTermVar var_ap;

termUptSt ::
  TamiglooDatatypes.IOSTerm ->
    TamiglooDatatypes.IOSTerm ->
      TamiglooDatatypes.IOSTerm -> TamiglooDatatypes.IOSTerm;
termUptSt lp rp state =
  TamiglooDatatypes.IOSTermSetOp TamiglooDatatypes.UpdateSt [lp, rp, state];

predPhiR ::
  [TamiglooDatatypes.RestrFormula] ->
    String -> TamiglooDatatypes.Rule -> TamiglooDatatypes.IOSFormula;
predPhiR restrs role rule =
  let {
    l = TamiglooDatatypes.IOSTermFacts (TamiglooDatatypes.accPr rule);
    a = TamiglooDatatypes.IOSTermClaims (TamiglooDatatypes.accAc rule);
    r = TamiglooDatatypes.IOSTermFacts (TamiglooDatatypes.accCncl rule);
    instRestrs = Restrictions.ruleRestrs restrs rule;
    iosfRestrs = Restrictions.iosfRestrictions instRestrs;
    x = map TamiglooDatatypes.createIOSTermVar
          (TamiglooDatatypes.getVarsVTermList
            (TamiglooDatatypes.accIOSTermFactsTermList l ++
              TamiglooDatatypes.accIOSTermFactsTermList a ++
                TamiglooDatatypes.accIOSTermFactsTermList r));
    guard =
      TamiglooDatatypes.IOSFand
        (TamiglooDatatypes.IOSFand (predM termVar_lp termVar_s)
          (TamiglooDatatypes.predEq termVar_lp l))
        (TamiglooDatatypes.IOSFand (TamiglooDatatypes.predEq termVar_ap a)
          (TamiglooDatatypes.predEq termVar_rp r));
    guardWithRestrs =
      (if Arith.equal_nat (List.size_list instRestrs) Arith.zero_nat then guard
        else TamiglooDatatypes.IOSFand guard iosfRestrs);
  } in wrapInForAll (x ++ [termVar_lp, termVar_ap, termVar_rp])
         (TamiglooDatatypes.IOSFimpl guardWithRestrs
           (TamiglooDatatypes.IOSFex termVar_pp
             (TamiglooDatatypes.IOSFsepConj
               [permR rule
                  ([termVar_p] ++
                    x ++ [termVar_lp, termVar_ap, termVar_rp, termVar_pp]),
                 absPredP role
                   [termVar_pp, termVar_rid,
                     termUptSt termVar_lp termVar_rp termVar_s]])));

wrapInEx ::
  [TamiglooDatatypes.IOSTerm] ->
    TamiglooDatatypes.IOSFormula -> TamiglooDatatypes.IOSFormula;
wrapInEx [] f = f;
wrapInEx (t : ts) f = TamiglooDatatypes.IOSFex t (wrapInEx ts f);

auxFactsWithDifferentTerms ::
  ([ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar)] ->
    [ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar)]) ->
    [TamiglooDatatypes.Fact] -> [TamiglooDatatypes.Fact];
auxFactsWithDifferentTerms f fl =
  map (\ inp ->
        TamiglooDatatypes.replaceTermsFact
          (f (TamiglooDatatypes.accTermList inp)) inp)
    fl;

predPhiRF :: String -> TamiglooDatatypes.Rule -> TamiglooDatatypes.IOSFormula;
predPhiRF role rule =
  let {
    rPrev = auxFactsWithDifferentTerms List.tl (TamiglooDatatypes.accCncl rule);
    r = auxFactsWithDifferentTerms
          (\ a -> TamiglooDatatypes.varToVTerm var_rid : a) rPrev;
    z = map TamiglooDatatypes.createIOSTermVar
          (TamiglooDatatypes.getVarsVTermList
            (concatMap TamiglooDatatypes.accTermList rPrev));
    fi = TamiglooDatatypes.IOSTermFacts r;
  } in wrapInEx (termVar_pp : z)
         (TamiglooDatatypes.IOSFsepConj
           [permRF rule ([termVar_p, termVar_rid] ++ z ++ [termVar_pp]),
             absPredP role
               [termVar_pp, termVar_rid,
                 TamiglooDatatypes.IOSTermSetOp TamiglooDatatypes.MUnion
                   [termVar_s, fi]]]);

predPhiRG :: String -> TamiglooDatatypes.Rule -> TamiglooDatatypes.IOSFormula;
predPhiRG role rule =
  let {
    lPrev = auxFactsWithDifferentTerms List.tl (TamiglooDatatypes.accPr rule);
    l = auxFactsWithDifferentTerms
          (\ a -> TamiglooDatatypes.varToVTerm var_rid : a) lPrev;
    x = map TamiglooDatatypes.createIOSTermVar
          (TamiglooDatatypes.getVarsVTermList
            (concatMap TamiglooDatatypes.accTermList lPrev));
    gi = TamiglooDatatypes.IOSTermFacts l;
  } in wrapInForAll x
         (TamiglooDatatypes.IOSFimpl
           (TamiglooDatatypes.IOSFpred TamiglooDatatypes.MIn [gi, termVar_s])
           (TamiglooDatatypes.IOSFex termVar_pp
             (TamiglooDatatypes.IOSFsepConj
               [permRG rule ([termVar_p, termVar_rid] ++ x ++ [termVar_pp]),
                 absPredP role
                   [termVar_pp, termVar_rid,
                     TamiglooDatatypes.IOSTermSetOp TamiglooDatatypes.MDiff
                       [termVar_s, gi]]])));

makeNameLVar :: ForeignImports.LVar -> String;
makeNameLVar (ForeignImports.LVar name lsort index) =
  let {
    withLSort =
      (if TamiglooDatatypes.equal_LSort lsort ForeignImports.LSortMsg then name
        else GenericHelperFunctions.prependToString name
               (TamiglooDatatypes.showLSort lsort));
  } in (if index == (0 :: Integer) then withLSort
         else GenericHelperFunctions.prependToString withLSort
                (GenericHelperFunctions.stringOfInteger index));

isAbsPredPhiRG :: TamiglooDatatypes.IOSFormula -> Bool;
isAbsPredPhiRG (TamiglooDatatypes.IOSFpred (TamiglooDatatypes.Pred name) uu) =
  GenericHelperFunctions.splitAndGetFst name == "phiRG";
isAbsPredPhiRG (TamiglooDatatypes.IOSFpred TamiglooDatatypes.Equal va) =
  error "undefined";
isAbsPredPhiRG (TamiglooDatatypes.IOSFpred TamiglooDatatypes.MIn va) =
  error "undefined";
isAbsPredPhiRG (TamiglooDatatypes.IOSFpred (TamiglooDatatypes.Perm vb vc) va) =
  error "undefined";
isAbsPredPhiRG (TamiglooDatatypes.IOSFpred TamiglooDatatypes.Token va) =
  error "undefined";
isAbsPredPhiRG (TamiglooDatatypes.IOSFRestr v) = error "undefined";
isAbsPredPhiRG (TamiglooDatatypes.IOSFand v va) = error "undefined";
isAbsPredPhiRG (TamiglooDatatypes.IOSFimpl v va) = error "undefined";
isAbsPredPhiRG (TamiglooDatatypes.IOSFsepConj v) = error "undefined";
isAbsPredPhiRG (TamiglooDatatypes.IOSFex v va) = error "undefined";
isAbsPredPhiRG (TamiglooDatatypes.IOSFfa v va) = error "undefined";

isAbsPredPhiRF :: TamiglooDatatypes.IOSFormula -> Bool;
isAbsPredPhiRF (TamiglooDatatypes.IOSFpred (TamiglooDatatypes.Pred name) uu) =
  GenericHelperFunctions.splitAndGetFst name == "phiRF";
isAbsPredPhiRF (TamiglooDatatypes.IOSFpred TamiglooDatatypes.Equal va) =
  error "undefined";
isAbsPredPhiRF (TamiglooDatatypes.IOSFpred TamiglooDatatypes.MIn va) =
  error "undefined";
isAbsPredPhiRF (TamiglooDatatypes.IOSFpred (TamiglooDatatypes.Perm vb vc) va) =
  error "undefined";
isAbsPredPhiRF (TamiglooDatatypes.IOSFpred TamiglooDatatypes.Token va) =
  error "undefined";
isAbsPredPhiRF (TamiglooDatatypes.IOSFRestr v) = error "undefined";
isAbsPredPhiRF (TamiglooDatatypes.IOSFand v va) = error "undefined";
isAbsPredPhiRF (TamiglooDatatypes.IOSFimpl v va) = error "undefined";
isAbsPredPhiRF (TamiglooDatatypes.IOSFsepConj v) = error "undefined";
isAbsPredPhiRF (TamiglooDatatypes.IOSFex v va) = error "undefined";
isAbsPredPhiRF (TamiglooDatatypes.IOSFfa v va) = error "undefined";

isAbsPredPhiR :: TamiglooDatatypes.IOSFormula -> Bool;
isAbsPredPhiR (TamiglooDatatypes.IOSFpred (TamiglooDatatypes.Pred name) uu) =
  GenericHelperFunctions.splitAndGetFst name == "phiR";
isAbsPredPhiR (TamiglooDatatypes.IOSFpred TamiglooDatatypes.Equal va) =
  error "undefined";
isAbsPredPhiR (TamiglooDatatypes.IOSFpred TamiglooDatatypes.MIn va) =
  error "undefined";
isAbsPredPhiR (TamiglooDatatypes.IOSFpred (TamiglooDatatypes.Perm vb vc) va) =
  error "undefined";
isAbsPredPhiR (TamiglooDatatypes.IOSFpred TamiglooDatatypes.Token va) =
  error "undefined";
isAbsPredPhiR (TamiglooDatatypes.IOSFRestr v) = error "undefined";
isAbsPredPhiR (TamiglooDatatypes.IOSFand v va) = error "undefined";
isAbsPredPhiR (TamiglooDatatypes.IOSFimpl v va) = error "undefined";
isAbsPredPhiR (TamiglooDatatypes.IOSFsepConj v) = error "undefined";
isAbsPredPhiR (TamiglooDatatypes.IOSFex v va) = error "undefined";
isAbsPredPhiR (TamiglooDatatypes.IOSFfa v va) = error "undefined";

expandPredPhi ::
  [TamiglooDatatypes.RestrFormula] ->
    (String, (TamiglooDatatypes.Rule, TamiglooDatatypes.IOSFormula)) ->
      (TamiglooDatatypes.IOSFormula, TamiglooDatatypes.IOSFormula);
expandPredPhi restrs t =
  let {
    role = fst t;
    rule = fst (snd t);
    absPhi = snd (snd t);
  } in (if isAbsPredPhiR absPhi then (absPhi, predPhiR restrs role rule)
         else (if isAbsPredPhiRG absPhi then (absPhi, predPhiRG role rule)
                else (if isAbsPredPhiRF absPhi
                       then (absPhi, predPhiRF role rule)
                       else error "undefined")));

getRolesIOSpec ::
  [TamiglooDatatypes.RestrFormula] ->
    (String,
      ([TamiglooDatatypes.Rule],
        ([TamiglooDatatypes.Rule], [TamiglooDatatypes.Rule]))) ->
      (String,
        ((TamiglooDatatypes.IOSFormula, TamiglooDatatypes.IOSFormula),
          ((TamiglooDatatypes.IOSFormula, TamiglooDatatypes.IOSFormula),
            [(TamiglooDatatypes.IOSFormula, TamiglooDatatypes.IOSFormula)])));
getRolesIOSpec restrs r =
  let {
    role = fst r;
    protoRules = fst (snd r);
    ioInRules = fst (snd (snd r));
    ioOutRules = snd (snd (snd r));
    absPhiTri = collectAbsPhi role protoRules ioInRules ioOutRules;
    _ = map (\ t -> snd (snd t)) absPhiTri;
  } in (role,
         (predPsi role,
           ((absPredP role [termVar_p, termVar_rid, termVar_s],
              predP role protoRules ioInRules ioOutRules),
             map (expandPredPhi restrs) absPhiTri)));

extractIOSpec ::
  TamiglooDatatypes.Theory ->
    [(String,
       ((TamiglooDatatypes.IOSFormula, TamiglooDatatypes.IOSFormula),
         ((TamiglooDatatypes.IOSFormula, TamiglooDatatypes.IOSFormula),
           [(TamiglooDatatypes.IOSFormula, TamiglooDatatypes.IOSFormula)])))];
extractIOSpec thy =
  let {
    restrs = TamiglooDatatypes.extractRestrs thy;
  } in List.foldr (\ a -> (\ b -> getRolesIOSpec restrs a : b))
         (Decomposition.extractProtoAndIoRules thy) [];

getAbsPWithDef ::
  ((TamiglooDatatypes.IOSFormula, TamiglooDatatypes.IOSFormula),
    ((TamiglooDatatypes.IOSFormula, TamiglooDatatypes.IOSFormula),
      [(TamiglooDatatypes.IOSFormula, TamiglooDatatypes.IOSFormula)])) ->
    (TamiglooDatatypes.IOSFormula, TamiglooDatatypes.IOSFormula);
getAbsPWithDef iospec = fst (snd iospec);

getAbsPsiWithDef ::
  ((TamiglooDatatypes.IOSFormula, TamiglooDatatypes.IOSFormula),
    ((TamiglooDatatypes.IOSFormula, TamiglooDatatypes.IOSFormula),
      [(TamiglooDatatypes.IOSFormula, TamiglooDatatypes.IOSFormula)])) ->
    (TamiglooDatatypes.IOSFormula, TamiglooDatatypes.IOSFormula);
getAbsPsiWithDef iospec = fst iospec;

getAbsPhisWithDef ::
  ((TamiglooDatatypes.IOSFormula, TamiglooDatatypes.IOSFormula),
    ((TamiglooDatatypes.IOSFormula, TamiglooDatatypes.IOSFormula),
      [(TamiglooDatatypes.IOSFormula, TamiglooDatatypes.IOSFormula)])) ->
    [(TamiglooDatatypes.IOSFormula, TamiglooDatatypes.IOSFormula)];
getAbsPhisWithDef iospec = snd (snd iospec);

createIOSTermVarFromName :: String -> TamiglooDatatypes.IOSTerm;
createIOSTermVarFromName name =
  TamiglooDatatypes.createIOSTermVar
    (TamiglooDatatypes.createLVarFromName name);

}
