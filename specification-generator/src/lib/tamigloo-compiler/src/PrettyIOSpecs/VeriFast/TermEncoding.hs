


module PrettyIOSpecs.VeriFast.TermEncoding (

          veriFastTermEncoding
        , veriFastPubEncoding
        , veriFastFreshEncoding
        , veriFastPlaceEncoding


        , funcDecls
        , funcACLemmas
        , nameACLemmas
        , ppRRule
  ) where

import Prelude
import qualified    Data.Set as S
import qualified    Data.ByteString.Char8 as BC
-- Tamarin prover imports
import              Text.PrettyPrint.Class
-- import              Term.Term.Raw
import              Term.Maude.Signature(MaudeSig, rrulesForMaudeSig, funSyms)
import              Term.Term.FunctionSymbols
-- import              Term.Builtin.Rules(RRule(..))
import              Term.LTerm (frees)
-- import              Term.VTerm(constsVTerm)
-- import              Term.Builtin.Convenience(x1, x2, x3)
import              Theory.Model.Signature(_sigMaudeInfo)
import qualified    Theory as T
-- Tamigloo imports
-- ---- isabelle generated
import              GenericHelperFunctions(nub)
import qualified    TamiglooDatatypes as TID
-- ---- other Tamigloo modules
import              PrettyIOSpecs.VeriFast.Utils






{- ---- Pub/Fresh to Term -}
{-  The Fresh and Pub types have to be lifted to Term types by providing constructors.
    This way Fresh and Pub values are usable in expressions requiring Terms -}
veriFastTermEncoding :: Document d => TID.Theory -> d
veriFastTermEncoding (TID.Theory _thyName fsig _thyItems) =
    let
        sigMaude = ( _sigMaudeInfo fsig)
        -- get function signatures from Maude signature
        funcSyms = S.toList (funSyms sigMaude)
    in
    ghostBlock $
        text "inductive Term = Term(list<boolean>);" $$ text "\n" $$
        text "fixpoint Term freshTerm(Fresh f);" $$
        text "fixpoint Term pubTerm(Pub p);" $$ text "\n\n" $$
        text "// Function declarations" $$
        (funcDecls "Term" funcSyms) $$
        text "\n\n" $$
        nest 4 (funcACLemmas ppACLemmas funcSyms) $$
        text "\n\n" $$
        nest 4 (eqEncoding sigMaude)


funcDecls :: Document d => String -> [FunSym] -> d
funcDecls typeId fSyms =
    vcat $ map ppFunSym fSyms
    where
        ppFunSym :: Document d => FunSym -> d
        ppFunSym (NoEq (f, (ar, _))) = 
            -- we do not make a distinction between private and public since we don't consider the adversary
            let 
                args = map ((++) (typeId ++ " ")) (convenienceNames ar "t")
            in
                fixpointNoBody typeId (reservedVeriFastWords (BC.unpack f)) args
        ppFunSym (AC o) = 
            -- AC function symbols are made to be binary
            -- This needs to happen in function declaration and application
            fixpointNoBody typeId (reservedVeriFastWords (show o)) [typeId ++ " x", typeId ++ " y"]
        ppFunSym (C EMap) = -- TODO not sure if we should print emapSymString or EMap
            fixpointNoBody typeId (reservedVeriFastWords (BC.unpack emapSymString)) [typeId ++ " x", typeId ++ " y"]
        ppFunSym (List) = -- TODO not sure about this one, but does not seem to be used anyway
            error $ functionApp "list" ["l seq["++ typeId ++"]"] -- NYI
funcACLemmas :: Document d => (FunSym -> d) -> [FunSym] -> d
funcACLemmas ppACLemma fSyms =
    let
        filterAC = (\fs -> case fs of
            AC _ -> True
            _ -> False)
    in 
        vcat $ map ppACLemma (filter filterAC fSyms)

ppACLemmas :: Document d => FunSym -> d
ppACLemmas (AC o) = nameACLemmas "Term" (reservedVeriFastWords (show o))
ppACLemmas _ = error "ppACLemmas called with wrong arguments."

nameACLemmas :: Document d => String -> String -> d
nameACLemmas typeId name =
    let
        lemmaNameA = (name ++ "_A")
        lemmaNameC = (name ++ "_C")
    in
    text ("// associativity and commutativity for function " ++ name) $$
    -- assoc
    (autoLemmaNoBody "void" lemmaNameA [typeId ++ " x", typeId ++ " y", typeId ++ " z"] "true" $
        "true && " ++
        (functionApp name ["x", functionApp name ["y", "z"] ]) ++ " == " ++
        (functionApp name [functionApp name ["x", "y"], "z" ])
    ) $$
    -- comm 
    (autoLemmaNoBody "void" lemmaNameC [typeId ++ " x", typeId ++ " y"] "true" $
        "true && " ++
        (functionApp name ["x", "y"]) ++ " == " ++
        (functionApp name ["y", "x"])
    )


            

{- ---- equation encoding -}
{-  The equations declared in Tamarin give semantic to the functions.
    Equations are represented as rewrite rules in the Maude singature
    (and as AC/C in the function symbols).
    In VeriFast, we write the rewrite rules as lemmas -}
eqEncoding :: Document d => MaudeSig -> d
eqEncoding sigMaude = 
    let 
        rrules = S.toList (rrulesForMaudeSig sigMaude)
    in
        vcat $ map (uncurry (ppRRule "Term")) (zip (convenienceNames (length rrules) "termFuncLemma") rrules)

{- ---- ---- pretty print rewriting rules -}
ppRRule :: Document d => String -> String -> T.RRule T.LNTerm -> d
ppRRule typeId lemmaName rr@(T.RRule lhs rhs) = 
    let
        vars = frees rr
        args = map ((++) (typeId ++ " ") . prettyVFLNTerm True . TID.varToVTerm) vars
        ens = (prettyVFLNTerm True lhs ++ " == " ++ prettyVFLNTerm True rhs)
    in
        autoLemmaNoBody "void" lemmaName args "true" ("true && " ++ ens)
        






        



{- pub encoding -}
{-  model a public Tamarin LNTerm e.g. $a in VeriFast. 
    Since Tamarin uses only abstract terms, the user has to provide concrete constructors
    from basic types e.g. int, string, etc. -}
veriFastPubEncoding :: Document d => TID.Theory -> d
veriFastPubEncoding thy =
    text "// TODO: provide constructors for Pub type e.g.:" $$
    (ghostBlock $
        text "inductive Pub =" $$
        nest 8 (text "pub_msg(String)") $$
        nest 4 (text "|   pub_int(int)\n\n") $$
        text "// Constants" $$
        nest 4 (constEncoding thy) <> text ";" 
    )
    where
        {- ---- constant encoding -}
        {- encode constants as null-ary constructors in Pub inductive type -}
        constEncoding :: Document d => TID.Theory -> d
        constEncoding theory = 
            let
                constants = nub (TID.extractConsts theory) 
            in
                (vcat $
                    map (text . ((++) "|   ") . reservedVeriFastWords . makeNameConst) constants) 




{- fresh encoding -}
{-  model a fresh Tamarin LNTerm e.g. ~x in VeriFast. 
    Since Tamarin uses only abstract terms, the user has to provide concrete constructors
    from basic types e.g. int, string, etc. -}
veriFastFreshEncoding :: Document d => d
veriFastFreshEncoding =
    text "// TODO: provide constructors for Fresh type e.g.:" $$
    (ghostBlock $
        text "inductive Fresh =" $$
        nest 8 (text "fr_msg(String)") $$
        nest 4 (text "|   fr_int(int);")
    )




{- place encoding -}
veriFastPlaceEncoding :: Document d => d
veriFastPlaceEncoding =
    ghostBlock $
        text "inductive Place = place(int);" $$
        text "predicate token(Place p);" $$ text "\n\n" $$
        iterSepConjDef


iterSepConjDef :: Document d => d
iterSepConjDef =
        text "predicate bigstar<T>(predicate(T) p, list<T> used);" $$ text "\n" $$
        text "lemma void bigstar_extract<T>(predicate(T) p, T value);" $$
        text "requires bigstar<T>(p, ?used) &*& !mem(value, used);" $$
        text "ensures bigstar<T>(p, cons(value, used)) &*& p(value);" $$ text "\n" 
