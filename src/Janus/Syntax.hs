-- | Defines the abstract syntax tree type of the type-synthesising ('ITerm')
-- and type-checking ('CTerm') terms, and substitution on these terms.
module Janus.Syntax
  ( BindingName
  , CTerm(..)
  , ITerm(..)
  , Name(..)
  , cSubst
  , cForgetLocalNames
  ) where

import           Janus.Semiring

-- | Name of a binding variable in a term.
type BindingName = String

-- | Variable name.
data Name
   = -- | Variable that has no binding occurrence in the term, represented by
     -- its 'String' name.
     Global String
   | -- | Variable that has a binding occurrence in the term, represented as
     -- De Bruijn index.
     Local BindingName Int
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
       BindingName -- ^ Name of the binding variable.
       CTerm -- ^ Body of the function.
   | -- | Dependent function type.
     Pi
       ZeroOneMany -- ^ Multiplicity of the function parameter.
       BindingName -- ^ Name of the variable binding the function argument in
                   -- the return type.
       CTerm -- ^ Type of the function parameter.
       CTerm -- ^ Type of the return value.
   | -- | Dependent multiplicative pair.
     MPair CTerm CTerm
   | -- | Dependent multiplicative pair type.
     MPairType
       ZeroOneMany -- ^ Multiplicity of the first element.
       BindingName -- ^ Name of the variable binding first element in the type
                   -- of the second element.
       CTerm -- ^ Type of the first element.
       CTerm -- ^ Type of the second element.
   | -- | Multiplicative unit.
     MUnit
   | -- | Multiplicative unit type.
     MUnitType
   | -- | Dependent additive pair.
     APair CTerm CTerm
   | -- | Dependent additive pair type.
     APairType
       BindingName -- ^ Name of the variable binding first element in the type
                   -- of the second element.
       CTerm -- ^ Type of the first element.
       CTerm -- ^ Type of the second element.
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
       BindingName -- ^ Name of the variable binding the pair in the type
                   -- annotation of the result of elimination.
       BindingName -- ^ Name of the variable binding the first element.
       BindingName -- ^ Name of the variable binding the second element.
       ITerm -- ^ The eliminated pair.
       CTerm -- ^ Result of the elimination.
       CTerm -- ^ Type annotation of the result of elimination.
   | -- | Multiplicative unit eliminator.
     MUnitElim
       ZeroOneMany -- ^ Multiplicity of the eliminated unit.
       BindingName -- ^ Name of the variable binding the unit in the type
                   -- annotation of the result of elimination.
       ITerm -- ^ The eliminated unit.
       CTerm -- ^ Result of the elimination.
       CTerm -- ^ Type annotation of the result of elimination.
   | -- | Additive pair eliminator evaluating into the first element.
     Fst ITerm
   | -- | Additive pair eliminator evaluating into the second element.
     Snd ITerm
   | -- | Disjoint sum eliminator.
     SumElim
        ZeroOneMany -- ^ Multiplicity of the sum contents.
        BindingName -- ^ Name of the variable binding the sum in the type
                    -- annotation of the result of elimination.
        ITerm -- ^ The eliminated sum.
        BindingName -- ^ Name of the variable binding the left element.
        CTerm -- ^ Result of the elimination in case the sum contains the left
              -- element.
        BindingName -- ^ Name of the variable binding the right element.
        CTerm -- ^ Result of the elimination in case the sum contains the right
              -- element.
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
iSubst ii r (MPairElim p z x y i c c') =
  MPairElim p z x y (iSubst ii r i) (cSubst (ii + 2) r c) (cSubst (ii + 1) r c')
iSubst ii r (MUnitElim p x i c c') =
  MUnitElim p x (iSubst ii r i) (cSubst ii r c) (cSubst (ii + 1) r c')
iSubst ii r (Fst i                     ) = Fst (iSubst ii r i)
iSubst ii r (Snd i                     ) = Snd (iSubst ii r i)
iSubst ii r (SumElim p z i x c y c' c'') = SumElim p
                                                   z
                                                   (iSubst ii r i)
                                                   x
                                                   (cSubst (ii + 1) r c)
                                                   y
                                                   (cSubst (ii + 1) r c')
                                                   (cSubst (ii + 1) r c'')

-- | Substitution on type-checkable terms.
--
-- @cSubst i m n@ replaces all occurrences of bound variable @i@ in the term @n@
-- with the term @m@.
cSubst :: Int -> ITerm -> CTerm -> CTerm
cSubst ii i' (Inf i  )       = Inf (iSubst ii i' i)
cSubst ii i' (Lam x c)       = Lam x (cSubst (ii + 1) i' c)
cSubst _  _  Universe        = Universe
cSubst ii r  (Pi p x ty ty') = Pi p x (cSubst ii r ty) (cSubst (ii + 1) r ty')
cSubst ii r  (MPair c c'   ) = MPair (cSubst ii r c) (cSubst ii r c')
cSubst ii r (MPairType p x ty ty') =
  MPairType p x (cSubst ii r ty) (cSubst (ii + 1) r ty')
cSubst _  _ MUnit        = MUnit
cSubst _  _ MUnitType    = MUnitType
cSubst ii r (APair c c') = APair (cSubst ii r c) (cSubst ii r c')
cSubst ii r (APairType x ty ty') =
  APairType x (cSubst ii r ty) (cSubst (ii + 1) r ty')
cSubst _  _ AUnit          = AUnit
cSubst _  _ AUnitType      = AUnitType
cSubst ii r (SumL c      ) = SumL (cSubst ii r c)
cSubst ii r (SumR c      ) = SumR (cSubst ii r c)
cSubst ii r (SumType c c') = SumType (cSubst ii r c) (cSubst ii r c')

-- | Replace all names of binding variables with an underscore.
cForgetLocalNames :: CTerm -> CTerm
cForgetLocalNames (Inf i  ) = Inf (iForgetLocalNames i)
cForgetLocalNames (Lam _ c) = Lam "_" (cForgetLocalNames c)
cForgetLocalNames Universe  = Universe
cForgetLocalNames (Pi p _ ty ty') =
  Pi p "_" (cForgetLocalNames ty) (cForgetLocalNames ty')
cForgetLocalNames (MPair c c') =
  MPair (cForgetLocalNames c) (cForgetLocalNames c')
cForgetLocalNames (MPairType p _ ty ty') =
  MPairType p "_" (cForgetLocalNames ty) (cForgetLocalNames ty')
cForgetLocalNames MUnit     = MUnit
cForgetLocalNames MUnitType = MUnitType
cForgetLocalNames (APair c c') =
  APair (cForgetLocalNames c) (cForgetLocalNames c')
cForgetLocalNames (APairType _ ty ty') =
  APairType "_" (cForgetLocalNames ty) (cForgetLocalNames ty')
cForgetLocalNames AUnit     = AUnit
cForgetLocalNames AUnitType = AUnitType
cForgetLocalNames (SumL c)  = SumL (cForgetLocalNames c)
cForgetLocalNames (SumR c)  = SumR (cForgetLocalNames c)
cForgetLocalNames (SumType c c') =
  SumType (cForgetLocalNames c) (cForgetLocalNames c')

-- | Replace all names of binding variables with an underscore.
iForgetLocalNames :: ITerm -> ITerm
iForgetLocalNames (Ann c c') = Ann (cForgetLocalNames c) (cForgetLocalNames c')
iForgetLocalNames (Bound j) = Bound j
iForgetLocalNames (Free (Local _ i)) = Free (Local "_" i)
iForgetLocalNames (Free x) = Free x
iForgetLocalNames (i :$: c) = iForgetLocalNames i :$: cForgetLocalNames c
iForgetLocalNames (MPairElim p _ _ _ i c c') = MPairElim
  p
  "_"
  "_"
  "_"
  (iForgetLocalNames i)
  (cForgetLocalNames c)
  (cForgetLocalNames c')
iForgetLocalNames (MUnitElim p _ i c c') = MUnitElim p
                                                     "_"
                                                     (iForgetLocalNames i)
                                                     (cForgetLocalNames c)
                                                     (cForgetLocalNames c')
iForgetLocalNames (Fst i                     ) = Fst (iForgetLocalNames i)
iForgetLocalNames (Snd i                     ) = Snd (iForgetLocalNames i)
iForgetLocalNames (SumElim p _ i _ c _ c' c'') = SumElim
  p
  "_"
  (iForgetLocalNames i)
  "_"
  (cForgetLocalNames c)
  "_"
  (cForgetLocalNames c')
  (cForgetLocalNames c'')

