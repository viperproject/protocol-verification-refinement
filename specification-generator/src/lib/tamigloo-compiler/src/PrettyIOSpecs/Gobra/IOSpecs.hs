
module PrettyIOSpecs.Gobra.IOSpecs (

    
        gobraIOSpecs
    ,   prettyGobraRestrs


  ) where

import              Prelude
import qualified    Data.Map as Map
import              Text.PrettyPrint.Class

import qualified    Theory as T
import qualified    Theory.Model.Formula as Form

import qualified    TamiglooDatatypes as TID
import qualified    IoSpecs as IOS
-- import              Arith (integer_of_nat)

import PrettyIOSpecs.Gobra.Utils
import PrettyIOSpecs.Gobra.TermEncoding
import PrettyIOSpecs.Gobra.FactEncoding
import PrettyIOSpecs.Gobra.PermissionEncoding







gobraIOSpecs :: Document d => Map.Map String String -> TID.Theory -> [(String, d)]
gobraIOSpecs config thy = 
  (let spec = prettyIOSpecs thy in
    map (\p -> (fst p, header (snd p))) spec
  )
  where
    header :: Document d => d -> d
    header spec = 
      gobraHeader config "iospec"
        ["claim", "fact", "term", "place", "pub", "fresh"]
        spec
        
prettyIOSpecs :: Document d => TID.Theory -> [(String, d)]
prettyIOSpecs thy = 
    map (\p -> (fst p, appTupel prettyIOSpecWithDef (snd p)))  (IOS.extractIOSpec thy)
    where
        appTupel :: Document d => (b -> c -> d) -> (a, (b, c)) -> d
        appTupel f (a, (b, c)) = f b c -- omit Psi


-- pretty I/O spec
prettyIOSpecWithDef :: Document d => (TID.IOSFormula, TID.IOSFormula) -> [(TID.IOSFormula, TID.IOSFormula)] -> d
prettyIOSpecWithDef predP phiList = 
    prettyPredWithDef predP $$
    (vcat $ map prettyPredWithDef phiList)

prettyPredWithDef :: Document d => (TID.IOSFormula, TID.IOSFormula) -> d
prettyPredWithDef (absPred, predDef) = 
        text "pred " <> prettyPredWithArgType absPred <> text " {"
    $$  nest 4 (prettyGobraIOSFormula predDef)
    $$  text "}"

prettyPredWithArgType :: Document d => TID.IOSFormula -> d
prettyPredWithArgType (TID.IOSFpred (TID.Pred name) ts) = 
    let
        argsWithType = (map prettyGobraIOSTermWithType ts)
        argsWithTypeGhost = init argsWithType ++ [(text "ghost " <> (last argsWithType))] -- last one is ghost s mset[Fact] 
    in
        functionAppDoc (text name) argsWithTypeGhost
prettyPredWithArgType _ = error "prettyPredWithArgType not called with IOSFPred Pred"

prettyGobraIOSFormula :: Document d => TID.IOSFormula -> d
prettyGobraIOSFormula f =
    case f of
        TID.IOSFpred _ _ -> prettyIOSFpred f
        TID.IOSFRestr f -> parens (prettyRestrForm f)
        TID.IOSFand a b -> prettyGobraIOSFormula a <> text " &&" $$ prettyGobraIOSFormula b
        TID.IOSFimpl a b -> parens (prettyGobraIOSFormula a) <> (text " ==>") $$ parens (prettyGobraIOSFormula b)
        TID.IOSFsepConj l -> prettySepConj f
        TID.IOSFex v inF -> prettyGobraIOSFormula inF -- exists only occurs for vars in Permissions for which we use getters
        TID.IOSFfa v inF -> (connectFa [v] inF)
    where
        {-
        connectEx :: Document d => [TID.IOSTerm] -> TID.IOSFormula -> d
        connectEx qs (TID.IOSFex v formula) = connectEx (qs ++ [v]) formula
        connectEx qs formula = 
            exists 
                (hcat . punctuate (text ", ") $ map prettyGobraIOSTermWithType qs) 
                (prettyGobraIOSFormula formula)
        -}
        connectFa :: Document d => [TID.IOSTerm] -> TID.IOSFormula -> d
        connectFa qs (TID.IOSFfa v formula) = connectFa (qs ++ [v]) formula
        connectFa qs formula =
            forallWithTriggerSetting All
                (hcat . punctuate (text ", ") $ map (prettyGobraIOSTermWithType) qs)
                [trigger formula]
                (prettyGobraIOSFormula formula)
        trigger :: Document d => TID.IOSFormula -> d
        trigger formula =
            let
                perm = head $ TID.filterIOSFpredsFromFormulas TID.isPerm [formula]
                pa = permApp perm
                isPermOut =
                    (\(TID.IOSFpred (TID.Perm permType _) _) ->
                        if permType == TID.Out_RG then True else False)
                getOutFact =
                    (\(TID.IOSFimpl (TID.IOSFpred TID.MIn ((TID.IOSTermFacts fs):_)) _) -> head fs)
            in
                if isPermOut perm
                then pa <> text " }{ " <> text (prettyFact True (getOutFact formula))
                else pa

prettyGobraRestrs :: Document d => TID.Theory -> d
prettyGobraRestrs (TID.Theory _ _ thyItems) = 
    text "==== Restrictions ==========\n" $$
    (nest 4 $ 
        vcat $ 
            map (\r -> text (getRestrName r) $$ (nest 4 $ prettyRestrForm (TID.getRestrFromItem r))) . 
            filter TID.isRestrItem $ 
            thyItems)
    where
        getRestrName :: TID.TheoryItem -> String
        getRestrName (TID.RestrItem name _) = name

prettyRestrForm :: Document d => TID.RestrFormula -> d
prettyRestrForm (TID.Ato atom) = prettyAtom atom
prettyRestrForm (TID.Not f) = text "!(" <> prettyRestrForm f <> text ")"
prettyRestrForm (TID.Conn conn l r) = parens (prettyRestrForm l) <> text (showConn conn) <> parens (prettyRestrForm r)
prettyRestrForm (TID.RFA t f) = text "(" <> (connectRFA [t] f) <> text ")"
    where
        connectRFA :: Document d => [T.LNTerm] -> TID.RestrFormula -> d
        connectRFA qs (TID.RFA v formula) = connectRFA (qs ++ [v]) formula
        connectRFA qs formula =
            forallWithTriggerSetting None 
                (hcat . punctuate (text ", ") $ map (text . prettyGobraLNTermWithType) qs)
                []
                (prettyRestrForm formula)


prettyAtom :: Document d => TID.Atom -> d
prettyAtom (TID.Atom f) = text (prettyFact True f)
prettyAtom (TID.EqE t1 t2) = text (prettyGobraLNTerm True t1) <> text " == " <> text (prettyGobraLNTerm True t2)
prettyAtom (TID.TF b) = if b then text "true" else text "false" 

showConn :: Form.Connective -> String
showConn Form.And = " && "
showConn Form.Or = " || "
showConn Form.Imp = " ==> "
showConn Form.Iff = " == "



prettySepConj :: Document d => TID.IOSFormula -> d
prettySepConj (TID.IOSFsepConj ls) =
    if TID.isPerm (head ls)
    then
        expectsBin ls (
            prettyGobraIOSFormula (head ls) <>
            text " && " $$
            prettyPredUsingGetters (head ls) (replacePermRetValues (head ls) (last ls))
        )
    else
        (vcat . punctuate (text " &&" ) $ map prettyGobraIOSFormula ls)


prettyPredUsingGetters :: Document d => TID.IOSFormula -> TID.IOSFormula -> d
prettyPredUsingGetters perm (TID.IOSFpred (TID.Pred name) ts) =
    functionAppDoc (text name) (map (prettyGobraIOSTermGeneric (prettyLNTermGetPerm perm)) ts)
    where
        isGetter :: TID.IOSFormula -> T.LNTerm -> Bool
        isGetter perm term = Map.member term (mappingRetTermsGetterTerms perm)
        sortOfGetter :: TID.IOSFormula -> T.LNTerm -> T.LSort
        sortOfGetter perm getterLNTerm =
            let
                maybeRet = Map.lookup getterLNTerm (mappingRetTermsGetterTerms perm)
            in
                T.sortOfLNTerm (maybe getterLNTerm id maybeRet)
        prettyLNTermGetPerm :: TID.IOSFormula -> T.LNTerm -> String
        prettyLNTermGetPerm perm term =
            if isGetter perm term
            then wrapFreshPub True (sortOfGetter perm term) $ prettyGobraLNTerm False term
            else prettyGobraLNTerm True term

        




prettyIOSFpred :: Document d => TID.IOSFormula -> d
prettyIOSFpred f@(TID.IOSFpred op ts) =
    case op of
        TID.Equal   -> expectsBin ts (
                        (prettyGobraIOSTerm True (head ts)) <> 
                        text " == " <>
                        (prettyGobraIOSTerm True (last ts)) 
                    )
        TID.MIn     -> expectsBin ts (
                            text "(" <> auxMIn "#" (head ts) (last ts) <> text ") > 0"
                    )
        TID.Perm _ _  -> permApp f
        TID.Token   -> functionAppDoc (text "token") (map (prettyGobraIOSTerm True) ts)
        TID.Pred n  -> functionAppDoc (text n) (map (prettyGobraIOSTerm True) ts)
    where
        auxMIn :: Document d => String -> TID.IOSTerm -> TID.IOSTerm -> d
        auxMIn opName (TID.IOSTermFacts fIn) fs = 
            (text $ prettyFact True (head fIn)) <> 
            text (" " ++ opName ++ " ") <> 
            (prettyGobraIOSTerm True fs)
            
prettyIOSFpred _ = error "prettyIOSFpred not called with IOSFPred"

























