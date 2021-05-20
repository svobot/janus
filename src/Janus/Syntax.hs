-- | Definitions of data types which are used throughout the code and functions
-- for substitution on and beta-reduction of terms.
module Janus.Syntax
  ( Binding(..)
  , CTerm(..)
  , ITerm(..)
  , Name(..)
  , cSubst
  ) where

import           Janus.Semiring

-- | Variable name.
data Name
   = -- | Variable that has no binding occurrence in the term, represented by
     -- its 'String' name.
     Global String
   | -- | Variable that has a binding occurrence in the term, represented as
     -- De Bruijn index.
     Local Int
   | -- | Internal constructor used when converting values to terms.
     Quote Int
  deriving (Show, Eq, Ord)

-- | Type-checkable term.
data CTerm
   = -- | Type-synthesising term is also type-checkable.
     Inf ITerm
   | -- | Type of types.
     Universe
   | -- | Function abstraction.
     Lam
       CTerm -- ^ Body of the function.
   | -- | Dependent function type.
     Pi
       ZeroOneMany -- ^ Multiplicity of the function parameter.
       CTerm -- ^ Type of the function parameter.
       CTerm -- ^ Type of the function body.
   | -- | Dependent multiplicative pair.
     MPair CTerm CTerm
   | -- | Dependent multiplicative pair type.
     MPairType
       ZeroOneMany -- ^ Multiplicity of the first element.
       CTerm -- ^ Type of the first element.
       CTerm -- ^ Type of the second element.
   | -- | Multiplicative unit.
     MUnit
   | -- | Multiplicative unit type.
     MUnitType
   | -- | Dependent additive pair.
     APair CTerm CTerm
   | -- | Dependent additive pair type.
     APairType CTerm CTerm
   | -- | Additive unit.
     AUnit
   | -- | Additive unit type.
     AUnitType
  deriving (Show, Eq)

-- | Type-synthesising term.
data ITerm
   = -- | Type-annotated term.
     Ann
       CTerm -- ^ Term.
       CTerm -- ^ Type annotation.
   | -- De Bruijn index representation of a variable that is bound in the term.
     Bound Int
   | -- Free variable represented by its name.
     Free Name
   | -- | Function application.
     ITerm :$: CTerm
   | -- | Multiplicative pair eliminator.
     MPairElim
       ITerm -- ^ Term evaluating into a pair.
       CTerm -- ^ Term evaluating into the result of the elimination, which has
             -- the two elements of the pair bound.
       CTerm -- ^ Type annotation of the result of elimination.
   | -- | Multiplicative unit eliminator.
     MUnitElim
       ITerm -- ^ Term evaluating into a unit.
       CTerm -- ^ Term evaluating into the result of the elimination.
       CTerm -- ^ Type annotation of the result of elimination.
   | -- | Additive pair eliminator evaluating into the first element.
     Fst ITerm
   | -- | Additive pair eliminator evaluating into the second element.
     Snd ITerm
  deriving (Show, Eq)

-- | A context element grouping a variable name, its type, and quantity.
data Binding n u t = Binding
  { bndName  :: n
  , bndUsage :: u
  , bndType  :: t
  }
  deriving Eq

instance (Show n, Show u, Show t) => Show (Binding n u t) where
  show (Binding n u t) = show u <> " " <> show n <> " : " <> show t

-- | Substitution on type-synthesising terms.
--
-- @iSubst i m n@ replaces all occurrences of bound variable @i@ in the term @n@
-- with the term @m@.
iSubst :: Int -> ITerm -> ITerm -> ITerm
iSubst ii i' (Ann c c') = Ann (cSubst ii i' c) (cSubst ii i' c')
iSubst ii i' (Bound j ) = if ii == j then i' else Bound j
iSubst _  _  (Free  y ) = Free y
iSubst ii i' (i :$: c ) = iSubst ii i' i :$: cSubst ii i' c
iSubst ii r (MPairElim i c c') =
  MPairElim (iSubst ii r i) (cSubst (ii + 2) r c) (cSubst (ii + 1) r c')
iSubst ii r (MUnitElim i c c') =
  MUnitElim (iSubst ii r i) (cSubst ii r c) (cSubst (ii + 1) r c')
iSubst ii r (Fst i) = Fst (iSubst ii r i)
iSubst ii r (Snd i) = Snd (iSubst ii r i)

-- | Substitution on type-checkable terms.
--
-- @cSubst i m n@ replaces all occurrences of bound variable @i@ in the term @n@
-- with the term @m@.
cSubst :: Int -> ITerm -> CTerm -> CTerm
cSubst ii i' (Inf i)       = Inf (iSubst ii i' i)
cSubst ii i' (Lam c)       = Lam (cSubst (ii + 1) i' c)
cSubst _  _  Universe      = Universe
cSubst ii r  (Pi p ty ty') = Pi p (cSubst ii r ty) (cSubst (ii + 1) r ty')
cSubst ii r  (MPair c c' ) = MPair (cSubst ii r c) (cSubst ii r c')
cSubst ii r (MPairType p ty ty') =
  MPairType p (cSubst ii r ty) (cSubst (ii + 1) r ty')
cSubst _  _ MUnit        = MUnit
cSubst _  _ MUnitType    = MUnitType
cSubst ii r (APair c c') = APair (cSubst ii r c) (cSubst ii r c')
cSubst ii r (APairType ty ty') =
  APairType (cSubst ii r ty) (cSubst (ii + 1) r ty')
cSubst _ _ AUnit     = AUnit
cSubst _ _ AUnitType = AUnitType

