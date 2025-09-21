{-# LANGUAGE StandaloneDeriving #-}
module DerivingInstances(

    IOSpecWithDefs
) where
import qualified TamiglooDatatypes as TID
-- import qualified Theory as T


deriving instance Eq TID.SetOpId
deriving instance Eq TID.EnvFactGroup
deriving instance Ord TID.EnvFactGroup
-- deriving instance Eq TID.FactTag -- for some reason instance was generated for this one but not the others
deriving instance Ord TID.FactTag
deriving instance Eq TID.FactGroup
deriving instance Ord TID.FactGroup
deriving instance Eq TID.Fact
deriving instance Eq TID.IOSTerm
deriving instance Eq TID.Atom
deriving instance Eq TID.RestrFormula
deriving instance Eq TID.PermType
deriving instance Eq TID.PredOpId
deriving instance Eq TID.IOSFormula

type IOSpecWithDefs =
    ( (TID.IOSFormula, TID.IOSFormula), 
        ( (TID.IOSFormula, TID.IOSFormula), [(TID.IOSFormula, TID.IOSFormula)] )
    )