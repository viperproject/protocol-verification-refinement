{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Restrictions(ruleRestrs, iosfRestrictions) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified ForeignImports;
import qualified Option;
import qualified Orderings;
import qualified HOL;
import qualified Arith;
import qualified List;
import qualified GenericHelperFunctions;
import qualified TamiglooDatatypes;

isFAPP ::
  ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar) ->
    Bool;
isFAPP t = (case t of {
             ForeignImports.LIT _ -> False;
             ForeignImports.FAPP _ _ -> True;
           });

getDbiLit ::
  ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar) ->
    Integer;
getDbiLit
  (ForeignImports.LIT (ForeignImports.Var (ForeignImports.LVar name lsort i))) =
  i;
getDbiLit (ForeignImports.LIT (ForeignImports.Con va)) = error "undefined";
getDbiLit (ForeignImports.FAPP v va) = error "undefined";

isDbiLit ::
  ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar) ->
    Bool;
isDbiLit
  (ForeignImports.LIT (ForeignImports.Var (ForeignImports.LVar name lsort i))) =
  (if name == "Bound" then True else False);
isDbiLit (ForeignImports.LIT (ForeignImports.Con va)) = False;
isDbiLit (ForeignImports.FAPP v va) = False;

safeGetDbiLit ::
  ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar) ->
    Maybe Integer;
safeGetDbiLit lnTerm =
  (if isDbiLit lnTerm then Just (getDbiLit lnTerm) else Nothing);

getDbis ::
  ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar) ->
    [Integer];
getDbis lnTerm =
  ((GenericHelperFunctions.collectThe .
     map (safeGetDbiLit . TamiglooDatatypes.varToVTerm)) .
    TamiglooDatatypes.getVarsVTerm)
    lnTerm;

hasFAPP :: TamiglooDatatypes.Fact -> Bool;
hasFAPP f =
  List.foldr (\ t -> (\ a -> isFAPP t || a)) (TamiglooDatatypes.accTermList f)
    False;

dbiToREX ::
  Integer ->
    ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar);
dbiToREX i =
  ForeignImports.LIT (ForeignImports.Var (ForeignImports.LVar "rEX" ForeignImports.LSortMsg i));

restrConj ::
  [TamiglooDatatypes.RestrFormula] -> Maybe TamiglooDatatypes.RestrFormula;
restrConj fs =
  (if Arith.equal_nat (List.size_list fs) Arith.zero_nat then Nothing
    else Just (List.foldr (TamiglooDatatypes.Conn ForeignImports.And)
                (List.butlast fs) (List.last fs)));

unwrapREX :: TamiglooDatatypes.RestrFormula -> TamiglooDatatypes.RestrFormula;
unwrapREX (TamiglooDatatypes.REX uu f) = unwrapREX f;
unwrapREX (TamiglooDatatypes.Ato v) = TamiglooDatatypes.Ato v;
unwrapREX (TamiglooDatatypes.Not v) = TamiglooDatatypes.Not v;
unwrapREX (TamiglooDatatypes.Conn v va vb) = TamiglooDatatypes.Conn v va vb;

wrapInREX ::
  [ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar)] ->
    TamiglooDatatypes.RestrFormula -> TamiglooDatatypes.RestrFormula;
wrapInREX [] f = f;
wrapInREX (t : ts) f = TamiglooDatatypes.REX t (wrapInREX ts f);

mappingREX ::
  TamiglooDatatypes.Fact ->
    [(Integer,
       ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar))];
mappingREX f =
  let {
    dbis =
      GenericHelperFunctions.nub
        (concat
          (List.map_filter
            (\ x -> (if isFAPP x then Just (getDbis x) else Nothing))
            (TamiglooDatatypes.accTermList f)));
  } in zip dbis (map dbiToREX dbis);

replaceDbiLNTerm ::
  Integer ->
    ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar) ->
      ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar) ->
        ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar);
replaceDbiLNTerm i repl original =
  (case original of {
    ForeignImports.LIT _ ->
      (if isDbiLit original && i == getDbiLit original then repl else original);
    ForeignImports.FAPP fun ts ->
      ForeignImports.FAPP fun (map (replaceDbiLNTerm i repl) ts);
  });

replaceDbiAtom ::
  Integer ->
    ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar) ->
      TamiglooDatatypes.Atom -> TamiglooDatatypes.Atom;
replaceDbiAtom i t a =
  (case a of {
    TamiglooDatatypes.Atom (TamiglooDatatypes.Fact fg ft ts) ->
      TamiglooDatatypes.Atom
        (TamiglooDatatypes.Fact fg ft (map (replaceDbiLNTerm i t) ts));
    TamiglooDatatypes.EqE t1 t2 ->
      TamiglooDatatypes.EqE (replaceDbiLNTerm i t t1) (replaceDbiLNTerm i t t2);
    TamiglooDatatypes.TF _ -> a;
  });

replaceDbi ::
  Integer ->
    ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar) ->
      TamiglooDatatypes.RestrFormula -> TamiglooDatatypes.RestrFormula;
replaceDbi i t f =
  (case f of {
    TamiglooDatatypes.Ato a -> TamiglooDatatypes.Ato (replaceDbiAtom i t a);
    TamiglooDatatypes.Not fa -> TamiglooDatatypes.Not (replaceDbi i t fa);
    TamiglooDatatypes.Conn conn l r ->
      TamiglooDatatypes.Conn conn (replaceDbi i t l) (replaceDbi i t r);
  });

instantiateWithMapping ::
  [(Integer,
     ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar))] ->
    TamiglooDatatypes.RestrFormula -> TamiglooDatatypes.RestrFormula;
instantiateWithMapping instMap restrDef =
  List.fold (GenericHelperFunctions.uncurry replaceDbi) instMap restrDef;

instantiateDbiLNTerms ::
  [(Integer,
     ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar))] ->
    ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar) ->
      ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar);
instantiateDbiLNTerms instMap lnTerm =
  List.foldr (GenericHelperFunctions.uncurry replaceDbiLNTerm) instMap lnTerm;

dbiToBoundLNTerm ::
  Integer ->
    ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar);
dbiToBoundLNTerm i =
  TamiglooDatatypes.varToVTerm
    (ForeignImports.LVar "Bound" ForeignImports.LSortNode i);

getDbiLitsPerFactArg :: TamiglooDatatypes.Fact -> [[Integer]];
getDbiLitsPerFactArg f = map getDbis (TamiglooDatatypes.accTermList f);

flipEnumInt :: forall a. Arith.Nat -> [a] -> [(a, Integer)];
flipEnumInt i ls =
  map (\ p -> (snd p, Arith.integer_of_nat (fst p)))
    (GenericHelperFunctions.enum i ls);

perArgMapping :: TamiglooDatatypes.Fact -> [[(Integer, Integer)]];
perArgMapping f =
  let {
    lens = map List.size_list (getDbiLitsPerFactArg f);
    maxCapturedVars =
      Arith.nat_of_integer
        ((1 :: Integer) +
          List.foldr Orderings.max (concat (getDbiLitsPerFactArg f))
            (0 :: Integer));
    minBounds =
      map (Arith.plus_nat maxCapturedVars)
        (List.butlast
          (GenericHelperFunctions.scanl Arith.plus_nat Arith.zero_nat lens));
    a = zip minBounds (getDbiLitsPerFactArg f);
  } in map (\ p -> flipEnumInt (fst p) (snd p)) a;

factToDistinctDbis :: TamiglooDatatypes.Fact -> TamiglooDatatypes.Fact;
factToDistinctDbis (TamiglooDatatypes.Fact fg ft ts) =
  let {
    mapToLNTerm =
      map (map (\ p -> (fst p, dbiToBoundLNTerm (snd p))))
        (perArgMapping (TamiglooDatatypes.Fact fg ft ts));
    zippedTs = zip mapToLNTerm ts;
    a = map (\ p -> instantiateDbiLNTerms (fst p) (snd p)) zippedTs;
  } in TamiglooDatatypes.Fact fg ft a;

separateRestr ::
  TamiglooDatatypes.RestrFormula ->
    (TamiglooDatatypes.Fact, TamiglooDatatypes.RestrFormula);
separateRestr (TamiglooDatatypes.Conn ForeignImports.Imp l r) =
  (case l of {
    TamiglooDatatypes.Ato (TamiglooDatatypes.Atom f) -> (f, r);
  });
separateRestr (TamiglooDatatypes.Ato v) = error "undefined";
separateRestr (TamiglooDatatypes.Not v) = error "undefined";
separateRestr (TamiglooDatatypes.Conn ForeignImports.And va vb) =
  error "undefined";
separateRestr (TamiglooDatatypes.Conn ForeignImports.Or va vb) =
  error "undefined";
separateRestr (TamiglooDatatypes.Conn ForeignImports.Iff va vb) =
  error "undefined";
separateRestr (TamiglooDatatypes.REX v va) = error "undefined";

combineRestr ::
  (TamiglooDatatypes.Fact, TamiglooDatatypes.RestrFormula) ->
    TamiglooDatatypes.RestrFormula;
combineRestr p =
  TamiglooDatatypes.Conn ForeignImports.Imp
    (TamiglooDatatypes.Ato (TamiglooDatatypes.Atom (fst p))) (snd p);

getVarsAtom :: TamiglooDatatypes.Atom -> [ForeignImports.LVar];
getVarsAtom (TamiglooDatatypes.Atom f) =
  concatMap TamiglooDatatypes.getVarsVTerm (TamiglooDatatypes.accTermList f);
getVarsAtom (TamiglooDatatypes.EqE l r) =
  TamiglooDatatypes.getVarsVTerm l ++ TamiglooDatatypes.getVarsVTerm r;
getVarsAtom (TamiglooDatatypes.TF v) = [];

getVarsRestr ::
  [ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar)] ->
    TamiglooDatatypes.RestrFormula ->
      [ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar)];
getVarsRestr acc (TamiglooDatatypes.Ato atom) =
  acc ++ map TamiglooDatatypes.varToVTerm (getVarsAtom atom);
getVarsRestr acc (TamiglooDatatypes.Not f) = getVarsRestr acc f;
getVarsRestr acc (TamiglooDatatypes.Conn uu l r) =
  getVarsRestr (getVarsRestr acc l) r;

mappingDbis :: TamiglooDatatypes.RestrFormula -> [(Integer, [Integer])];
mappingDbis restr =
  let {
    sepRestr = separateRestr restr;
    fact = fst sepRestr;
    rhs = snd sepRestr;
    perArgMap = perArgMapping fact;
    catPerArg = concat perArgMap;
    maxDbisLhs =
      List.foldr (Orderings.max . Arith.nat_of_integer)
        (GenericHelperFunctions.sndList catPerArg) Arith.zero_nat;
    dbisRhs =
      GenericHelperFunctions.collectThe
        (map safeGetDbiLit (getVarsRestr [] rhs));
    dbisRhsNotInFact =
      GenericHelperFunctions.nub
        (List.foldr (\ a -> filter (\ b -> a == b))
          (GenericHelperFunctions.fstList catPerArg) dbisRhs);
    _ = map (\ p -> (fst p, [snd p]))
          (flipEnumInt (Arith.plus_nat maxDbisLhs Arith.one_nat)
            dbisRhsNotInFact);
    mergedArgMapping = GenericHelperFunctions.sortIntoBuckets catPerArg;
  } in mergedArgMapping;

restrToDistinctDbis ::
  TamiglooDatatypes.RestrFormula -> TamiglooDatatypes.RestrFormula;
restrToDistinctDbis restr =
  let {
    sepRestr = separateRestr restr;
    newFact = factToDistinctDbis (fst sepRestr);
    newLNTermMap =
      map (\ p -> (fst p, dbiToBoundLNTerm (snd p)))
        (map (\ p -> (fst p, List.hd (snd p))) (mappingDbis restr));
    newRhs = instantiateWithMapping newLNTermMap (snd sepRestr);
  } in combineRestr (newFact, newRhs);

createEqCheckList ::
  [ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar)] ->
    [TamiglooDatatypes.RestrFormula];
createEqCheckList lnTerms =
  (case lnTerms of {
    [] -> [];
    [_] -> [];
    x : y : zs ->
      TamiglooDatatypes.Ato (TamiglooDatatypes.EqE x y) :
        createEqCheckList (y : zs);
  });

dbisCreateEqChecks :: [Integer] -> Maybe TamiglooDatatypes.RestrFormula;
dbisCreateEqChecks dbis = let {
                            a = createEqCheckList (map dbiToBoundLNTerm dbis);
                          } in restrConj a;

createEqChecks ::
  [(Integer, [Integer])] -> Maybe TamiglooDatatypes.RestrFormula;
createEqChecks oldToNewMap =
  let {
    perArgEqChecks =
      GenericHelperFunctions.collectThe
        (map dbisCreateEqChecks (GenericHelperFunctions.sndList oldToNewMap));
  } in (if Arith.equal_nat (List.size_list perArgEqChecks) Arith.zero_nat
         then Nothing else restrConj perArgEqChecks);

linearizeRestr ::
  TamiglooDatatypes.RestrFormula -> TamiglooDatatypes.RestrFormula;
linearizeRestr restr =
  let {
    eqChecks = createEqChecks (mappingDbis restr);
    sepNewRestr = separateRestr (restrToDistinctDbis restr);
    rhs = (if GenericHelperFunctions.isSome eqChecks
            then TamiglooDatatypes.Conn ForeignImports.Imp (Option.the eqChecks)
                   (snd sepNewRestr)
            else snd sepNewRestr);
  } in combineRestr (fst sepNewRestr, rhs);

createEqPatternREX ::
  TamiglooDatatypes.Fact ->
    TamiglooDatatypes.RestrFormula -> TamiglooDatatypes.RestrFormula;
createEqPatternREX actFact restrREX =
  let {
    defFactTerms =
      TamiglooDatatypes.accTermList (fst (separateRestr (unwrapREX restrREX)));
    actFactTerms = TamiglooDatatypes.accTermList actFact;
    zipFAPPActDefTerms = filter (isFAPP . snd) (zip actFactTerms defFactTerms);
    eqs = map (\ p ->
                TamiglooDatatypes.Ato (TamiglooDatatypes.EqE (fst p) (snd p)))
            zipFAPPActDefTerms;
  } in Option.the (restrConj eqs);

instantiationMapLNTerm ::
  ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar) ->
    ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar) ->
      [(Integer,
         ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar))];
instantiationMapLNTerm (ForeignImports.LIT var) appTerm =
  [(getDbiLit (ForeignImports.LIT var), appTerm)];
instantiationMapLNTerm (ForeignImports.FAPP fs ts) uu = [];

instantiationMap ::
  TamiglooDatatypes.Fact ->
    TamiglooDatatypes.Fact ->
      [(Integer,
         ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar))];
instantiationMap dbiFact appFact =
  let {
    dbiTermList = TamiglooDatatypes.accTermList dbiFact;
    appTermList = TamiglooDatatypes.accTermList appFact;
  } in concatMap (GenericHelperFunctions.uncurry instantiationMapLNTerm)
         (zip dbiTermList appTermList);

createRestrREX ::
  TamiglooDatatypes.RestrFormula -> TamiglooDatatypes.RestrFormula;
createRestrREX restr =
  let {
    sepRestr = separateRestr restr;
    rexMap = mappingREX (fst sepRestr);
    a = List.fold (GenericHelperFunctions.uncurry replaceDbi) rexMap restr;
  } in wrapInREX (GenericHelperFunctions.sndList rexMap) a;

instantiateHasFAPP ::
  TamiglooDatatypes.Fact ->
    TamiglooDatatypes.RestrFormula -> TamiglooDatatypes.RestrFormula;
instantiateHasFAPP actFact linRestr =
  let {
    restrREX = createRestrREX linRestr;
    eqsPattern = createEqPatternREX actFact restrREX;
    unwrapRestrREX = separateRestr (unwrapREX restrREX);
    restrREXwithEq =
      TamiglooDatatypes.Conn ForeignImports.Imp eqsPattern (snd unwrapRestrREX);
    instMap = instantiationMap (fst (separateRestr linRestr)) actFact;
    instRestr = instantiateWithMapping instMap restrREXwithEq;
    rexVars =
      GenericHelperFunctions.sndList
        (mappingREX (fst (separateRestr linRestr)));
  } in wrapInREX rexVars instRestr;

instantiateRestr ::
  TamiglooDatatypes.Fact ->
    TamiglooDatatypes.RestrFormula -> TamiglooDatatypes.RestrFormula;
instantiateRestr f def =
  let {
    sepRestr = separateRestr def;
    instMap = instantiationMap (fst sepRestr) f;
  } in (if hasFAPP (fst sepRestr) then instantiateHasFAPP f def
         else instantiateWithMapping instMap (snd sepRestr));

eqFactRestr :: TamiglooDatatypes.Fact -> TamiglooDatatypes.RestrFormula -> Bool;
eqFactRestr f restr = TamiglooDatatypes.eqFactSig f (fst (separateRestr restr));

instantiateRestrictions ::
  [TamiglooDatatypes.RestrFormula] ->
    TamiglooDatatypes.Fact -> [TamiglooDatatypes.RestrFormula];
instantiateRestrictions restrs actFact =
  List.map_filter
    (\ x ->
      (if eqFactRestr actFact x then Just (instantiateRestr actFact x)
        else Nothing))
    restrs;

factListRestrs ::
  [TamiglooDatatypes.Fact] ->
    [TamiglooDatatypes.RestrFormula] -> [TamiglooDatatypes.RestrFormula];
factListRestrs acts restrs = concatMap (instantiateRestrictions restrs) acts;

ruleRestrs ::
  [TamiglooDatatypes.RestrFormula] ->
    TamiglooDatatypes.Rule -> [TamiglooDatatypes.RestrFormula];
ruleRestrs restrs r =
  factListRestrs (TamiglooDatatypes.accAc r) (map linearizeRestr restrs);

iosfRestrictions ::
  [TamiglooDatatypes.RestrFormula] -> TamiglooDatatypes.IOSFormula;
iosfRestrictions restrs =
  let {
    iosfRestrs = map TamiglooDatatypes.IOSFRestr restrs;
    n = List.size_list iosfRestrs;
  } in (if Arith.equal_nat n Arith.zero_nat then error "undefined"
         else List.foldl TamiglooDatatypes.IOSFand (List.hd iosfRestrs)
                (List.tl iosfRestrs));

}
