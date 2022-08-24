module PrettyIOSpecs.VeriFast.IOSpecs (

    
        veriFastIOSpecs
    ,   module PrettyIOSpecs.VeriFast.TermEncoding
    ,   module PrettyIOSpecs.VeriFast.FactEncoding
    ,   module PrettyIOSpecs.VeriFast.PermissionEncoding



  ) where

import              Prelude
import qualified    Data.Map as Map
import              Text.PrettyPrint.Class
import              Data.List(delete)
import              Data.List.Split


import qualified    Theory as T
import qualified    Theory.Model.Formula as Form

import qualified    TamiglooDatatypes as TID
import qualified    GenericHelperFunctions as GHF
import qualified    IoSpecs as IOS
-- import              Arith (integer_of_nat)

import PrettyIOSpecs.VeriFast.Utils
import PrettyIOSpecs.VeriFast.TermEncoding
import PrettyIOSpecs.VeriFast.FactEncoding
import PrettyIOSpecs.VeriFast.PermissionEncoding

veriFastIOSpecs :: Document d => TID.Theory -> [(String, d)]
veriFastIOSpecs = prettyIOSpecs
prettyIOSpecs :: Document d => TID.Theory -> [(String, d)]
prettyIOSpecs thy = 
    map (\p -> (fst p, appTupel prettyIOSpecWithDef (snd p) (fst p)))  (IOS.extractIOSpec thy)
    where
        appTupel :: Document d => (b -> c -> (String -> d)) -> (a, (b, c)) -> (String -> d)
        appTupel f (a, (b, c)) = f b c -- omit Psi

-- pretty I/O spec
prettyIOSpecWithDef :: Document d => (TID.IOSFormula, TID.IOSFormula) -> [(TID.IOSFormula, TID.IOSFormula)] -> String -> d
prettyIOSpecWithDef predP phiList role =
    ghostBlock $
        containerForQuants role phiList $$
        prettyPredP predP $$
        (vcat $ map (prettyPredCtor phiList role) phiList)

containerForQuants :: Document d => String -> [(TID.IOSFormula, TID.IOSFormula)] -> d
containerForQuants role phiList =
    let
        forms = (GHF.sndList phiList)
        absPreds = GHF.fstList phiList
        constrNames = map nameContainerConstr absPreds
        quantTypes = map ((map printTypeOfIOSTerm) . collectFa []) forms
        commentNames = map (\f -> (text " // ") <> (sepTerms $ map (prettyVFIOSTerm False) $ collectFa [] f)) forms
        constrs = map text $ map (uncurry auxFuncApp) (zip constrNames quantTypes)
        constrsWithComm = map (\p -> fst p <> snd p) (zip constrs commentNames)
    in
        text ("inductive " ++ role ++ "_quantified_vals =") $$
        nest 8 (head constrsWithComm) $$
        nest 4 (vcat $ map (\c -> text "|   " <> c) $ tail constrsWithComm) $$ text ";"
    where
        auxFuncApp name args =
            if length args == 0
            then name
            else functionApp name args

quantCases :: Document d => [(TID.IOSFormula, TID.IOSFormula)] -> (TID.IOSFormula, TID.IOSFormula) -> [(d, d)]
quantCases preds skipPred =
    let
        predSkipped = delete skipPred preds
    in
        map (\p -> quantCase p (text "return true;")) predSkipped 

quantCase :: Document d => (TID.IOSFormula, TID.IOSFormula) -> d -> (d, d)
quantCase (absPred, predDef) body =
    let
        qConsName = nameContainerConstr absPred
        qs = collectFa [] predDef
        qCons = auxQCons qConsName qs
    in
        (qCons, body)
    where
        auxQCons :: Document d => String -> [TID.IOSTerm] -> d
        auxQCons n args =
            if length args == 0
            then text n
            else text (n ++ "(") <> (sepTerms $ map (prettyVFIOSTerm False) args) <> text ")"


collectFa :: [TID.IOSTerm] -> TID.IOSFormula -> [TID.IOSTerm]
collectFa qs (TID.IOSFfa v formula) = collectFa (qs ++ [v]) formula
collectFa qs _ = qs

nameContainerConstr :: TID.IOSFormula -> String
nameContainerConstr (TID.IOSFpred (TID.Pred name) ts) = GHF.prependToString "quant" name



prettyPredP :: Document d => (TID.IOSFormula, TID.IOSFormula) -> d
prettyPredP = prettyPred wrapIterSCprettyF
    where
        wrapIterSCprettyF :: Document d => TID.IOSFormula -> d
        wrapIterSCprettyF f@(TID.IOSFsepConj _) = prettySepConjIterSepConj f
        wrapIterSCprettyF f = prettyVFIOSFormula f


prettyPredCtor :: Document d => [(TID.IOSFormula, TID.IOSFormula)] -> String -> (TID.IOSFormula, TID.IOSFormula) -> d
prettyPredCtor allPreds role c@(absPred, predDef) =
    let
        qConsType = role ++ "_quantified_vals"
        qCons = quantCase c (text "return" $$ prettyVFIOSFormula predDef <> text ";")
    in
        functionAppDoc (text "predicate_ctor " <> prettyPredWithArgType absPred) [text (qConsType ++ " q")] <>
        text " =" $$
        nest 4 (
            switchStmtDoc (text "q") (qCons : (quantCases allPreds c))
        ) $$ 
        text ";"
        

prettyPred :: Document d => (TID.IOSFormula -> d) -> (TID.IOSFormula, TID.IOSFormula) -> d
prettyPred f (absPred, predDef) =
        text "predicate " <> prettyPredWithArgType absPred <> text " ="
    $$  nest 4 (f predDef)
    $$  text ";"


prettyPredWithArgType :: Document d => TID.IOSFormula -> d
prettyPredWithArgType (TID.IOSFpred (TID.Pred name) ts) = 
    let
        argsWithType = (map prettyVFIOSTermWithType ts)
    in
        functionAppDoc (text name) argsWithType
prettyPredWithArgType _ = error "prettyPredWithArgType not called with IOSFPred Pred"

prettyVFIOSFormula :: Document d => TID.IOSFormula -> d
prettyVFIOSFormula f =
    case f of
        TID.IOSFpred _ _ -> prettyIOSFpred f
        TID.IOSFRestr f -> parens (prettyRestrForm f)
        TID.IOSFand a b -> prettyVFIOSFormula a <> text " &&" $$ prettyVFIOSFormula b
        TID.IOSFimpl a b -> (prettyVFIOSFormula a) $$ (text "?") $$ parens (prettyVFIOSFormula b) $$ text ":" $$ text "true"
        TID.IOSFsepConj _ -> prettySepConj f
        TID.IOSFex v inF -> prettyVFIOSFormula inF -- exists only occurs for vars in Permissions for which we use getters
        TID.IOSFfa v inF -> (connectFa [v] inF)
    where
        connectFa :: Document d => [TID.IOSTerm] -> TID.IOSFormula -> d
        connectFa qs (TID.IOSFfa v formula) = connectFa (qs ++ [v]) formula
        connectFa qs formula = (prettyVFIOSFormula formula)



-- restrictions
{- only for debugging
prettyVFRestrs :: Document d => TID.Theory -> d
prettyVFRestrs (TID.Theory _ _ thyItems) = 
    text "==== Restrictions ==========\n" $$
    (nest 4 $ 
        vcat $ 
            map (\r -> text (getRestrName r) $$ (nest 4 $ prettyRestrForm (TID.getRestrFromItem r))) . 
            filter TID.isRestrItem $ 
            thyItems)
    where
        getRestrName :: TID.TheoryItem -> String
        getRestrName (TID.RestrItem name _) = name
-}



prettyRestrForm :: Document d => TID.RestrFormula -> d
prettyRestrForm (TID.Ato atom) = prettyAtom atom
prettyRestrForm (TID.Not f) = text "!(" <> prettyRestrForm f <> text ")"
prettyRestrForm (TID.Conn conn l r) = prettyConn conn (parens (prettyRestrForm l)) (parens (prettyRestrForm r))
prettyRestrForm (TID.REX t f) = error "Patterns in definitions of restrictions not supported in VeriFast." -- text "(" <> (connectREX [t] f) <> text ")"
    where
        connectREX :: Document d => [T.LNTerm] -> TID.RestrFormula -> d
        connectREX qs (TID.REX v formula) = connectREX (qs ++ [v]) formula
        connectREX qs formula = exQuantFirst (map (prettyVFLNTerm True) qs) (prettyRestrForm formula)
        -- copied from Main.Console
        renderDoc :: Doc -> String
        renderDoc = renderStyle (defaultStyle)
        -- not ideal but have to prepend '?' to first occurence of existentially quanitified vars
        exQuantFirst :: Document d => [String] -> Doc -> d
        exQuantFirst qs df = text $ foldr (\a b -> auxEQF a b) (renderDoc df) qs
        auxEQF :: String -> String -> String
        auxEQF q s =
            (concat $ auxChangeFirst q $ split (onSublist q) s) 
        auxChangeFirst :: String -> [String] -> [String]
        auxChangeFirst _ [] = []
        auxChangeFirst q (x:xs) =
            if x == q 
            then ("?"++x) : xs 
            else x : (auxChangeFirst q xs)

prettyAtom :: Document d => TID.Atom -> d
prettyAtom (TID.Atom f) = text (prettyFact True f)
prettyAtom (TID.EqE t1 t2) = text (prettyVFLNTerm True t1) <> text " == " <> text (prettyVFLNTerm True t2)
prettyAtom (TID.TF b) = if b then text "true" else text "false" 

prettyConn :: Document d => Form.Connective -> d -> d -> d
prettyConn Form.And l r = l <> text " &&" $$ r
prettyConn Form.Or l r = l <> text " || " <> r
prettyConn Form.Imp l r = l <> text " ? " <> r <> text " : true"
prettyConn Form.Iff l r = l <> text " == " <> r


prettySepConj :: Document d => TID.IOSFormula -> d
prettySepConj (TID.IOSFsepConj ls) =
        (vcat . punctuate (text " &*&" ) $ map prettyVFIOSFormula ls)

prettySepConjIterSepConj :: Document d => TID.IOSFormula -> d
prettySepConjIterSepConj (TID.IOSFsepConj ls) =
        (vcat . punctuate (text " &*&" ) $
                map (\l -> functionAppDoc (text "bigstar") [prettyVFIOSFormula l, text "nil"] ) ls)


-- pred
prettyIOSFpred :: Document d => TID.IOSFormula -> d
prettyIOSFpred f@(TID.IOSFpred op ts) =
    case op of
        TID.Equal   -> expectsBin ts (
                        (prettyVFIOSTerm True (head ts)) <> 
                        text " ==" $$
                        (prettyVFIOSTerm True (last ts)) 
                    )
        TID.MIn     -> expectsBin ts (
                            auxMIn (head ts) (last ts)
                    )
        TID.Perm _ _  -> permAppQ f
        TID.Token   -> functionAppDoc (text "token") (map (prettyVFIOSTerm True) ts)
        TID.Pred n  ->  if GHF.splitAndGetFst n == "P"
                        then functionAppDocMLine (text n) (map (prettyVFIOSTerm True) ts)
                        else functionAppDoc(text n) (map (prettyVFIOSTerm True) ts)
    where
        auxMIn :: Document d => TID.IOSTerm -> TID.IOSTerm -> d
        auxMIn (TID.IOSTermFacts fIn) fs =
                functionAppDocMLine (text "msetIn") [text (prettyFact True (head fIn)), (prettyVFIOSTerm True fs)]            
prettyIOSFpred _ = error "prettyIOSFpred not called with IOSFPred"







