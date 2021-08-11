-- | Defines the abstract syntax tree type of the type-synthesising ('ITerm')
-- and type-checking ('CTerm') terms, and substitution on these terms.
module Janus.Syntax
  ( CTerm(..)
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
   | -- | Left constructor of a disjoint sum.
     SumL CTerm
   | -- | Right constructor of a disjoint sum.
     SumR CTerm
   | -- | Disjoint sum type.
     SumType CTerm CTerm
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
       ZeroOneMany -- ^ Multiplicity of the eliminated pair.
       ITerm -- ^ Term evaluating into a pair.
       CTerm -- ^ Term evaluating into the result of the elimination, which has
             -- the two elements of the pair bound.
       CTerm -- ^ Type annotation of the result of elimination.
   | -- | Multiplicative unit eliminator.
     MUnitElim
       ZeroOneMany -- ^ Multiplicity of the eliminated unit.
       ITerm -- ^ Term evaluating into a unit.
       CTerm -- ^ Term evaluating into the result of the elimination.
       CTerm -- ^ Type annotation of the result of elimination.
   | -- | Additive pair eliminator evaluating into the first element.
     Fst ITerm
   | -- | Additive pair eliminator evaluating into the second element.
     Snd ITerm
   | -- | Disjoint sum eliminator.
     SumElim
        ZeroOneMany -- ^ Multiplicity of the sum contents.
        ITerm -- ^ Term evaluating into a sum.
        CTerm -- ^ Term evaluating into the result in case the sum contains the
              -- left 
        CTerm -- ^
        CTerm -- ^ Type annotation of the result of the elimination.
  deriving (Show, Eq)

-- | Substitution on type-synthesising terms.
--
-- @iSubst i m n@ replaces all occurrences of bound variable @i@ in the term @n@
-- with the term @m@.
iSubst :: Int -> ITerm -> ITerm -> ITerm
iSubst ii i' (Ann c c') = Ann (cSubst ii i' c) (cSubst ii i' c')
iSubst ii i' (Bound j ) = if ii == j then i' else Bound j
iSubst _  _  (Free  y ) = Free y
iSubst ii i' (i :$: c ) = iSubst ii i' i :$: cSubst ii i' c
iSubst ii r (MPairElim p i c c') =
  MPairElim p (iSubst ii r i) (cSubst (ii + 2) r c) (cSubst (ii + 1) r c')
iSubst ii r (MUnitElim p i c c') =
  MUnitElim p (iSubst ii r i) (cSubst ii r c) (cSubst (ii + 1) r c')
iSubst ii r (Fst i               ) = Fst (iSubst ii r i)
iSubst ii r (Snd i               ) = Snd (iSubst ii r i)
iSubst ii r (SumElim p i c c' c'') = SumElim p
                                             (iSubst ii r i)
                                             (cSubst (ii + 1) r c)
                                             (cSubst (ii + 1) r c')
                                             (cSubst (ii + 1) r c'')

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
cSubst _  _ AUnit          = AUnit
cSubst _  _ AUnitType      = AUnitType
cSubst ii r (SumL c      ) = SumL (cSubst ii r c)
cSubst ii r (SumR c      ) = SumR (cSubst ii r c)
cSubst ii r (SumType c c') = SumType (cSubst ii r c) (cSubst ii r c')

