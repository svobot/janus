-- | Definitions of data types which are used throughout the code and functions
-- for substitution on and beta-reduction of terms.
module Janus.Types
  ( Binding(..)
  , BoundEnv
  , Context
  , CTerm(..)
  , ITerm(..)
  , Name(..)
  , Neutral(..)
  , Type
  , TypeEnv
  , Value(..)
  , ValueEnv
  , cEval
  , cSubst
  , iEval
  , vfree
  , quote0
  ) where

import           Data.Bifunctor                 ( second )
import           Janus.Semiring

data Name
   =  Global String
   |  Local Int
   |  Quote Int
  deriving (Show, Eq, Ord)

data CTerm
   =  Inf ITerm
   |  Universe
   |  Lam CTerm
   |  Pi ZeroOneMany CTerm CTerm
   |  MPair CTerm CTerm
   |  MPairType ZeroOneMany CTerm CTerm
   |  MUnit
   |  MUnitType
   |  APair CTerm CTerm
   |  APairType CTerm CTerm
   |  AUnit
   |  AUnitType
  deriving (Show, Eq)

data ITerm
   =  Ann CTerm CTerm
   |  Bound Int
   |  Free Name
   |  ITerm :$: CTerm
   |  MPairElim ITerm CTerm CTerm
   |  MUnitElim ITerm CTerm CTerm
   |  Fst ITerm
   |  Snd ITerm
  deriving (Show, Eq)

data Value
   =  VUniverse
   |  VNeutral Neutral
   |  VLam (Value -> Value)
   |  VPi ZeroOneMany Value (Value -> Value)
   |  VMPair Value Value
   |  VMPairType ZeroOneMany Value (Value -> Value)
   |  VMUnit
   |  VMUnitType
   |  VAPair Value Value
   |  VAPairType Value (Value -> Value)
   |  VAUnit
   |  VAUnitType

instance Show Value where
  show = show . quote0

data Neutral
   =  NFree Name
   |  NApp Neutral Value
   |  NMPairElim Neutral (Value -> Value -> Value) (Value -> Value)
   |  NMUnitElim Neutral Value (Value -> Value)
   |  NFst Neutral
   |  NSnd Neutral

data Binding n u t = Binding
  { bndName  :: n
  , bndUsage :: u
  , bndType  :: t
  }
  deriving Eq

instance (Show n, Show u, Show t) => Show (Binding n u t) where
  show (Binding n u t) = show u <> " " <> show n <> " : " <> show t

type Type = Value

type TypeEnv = [Binding Name ZeroOneMany Type]
type ValueEnv = [(Name, Value)]
type BoundEnv = [Value]
type Context = (ValueEnv, TypeEnv)

vfree :: Name -> Value
vfree n = VNeutral (NFree n)

-- | Evaluate a type-checkable term in a given context.
--
-- Context is a pair in which first element contains values of global variables
-- and second element contains values of local variables.
cEval :: (ValueEnv, BoundEnv) -> CTerm -> Value
cEval ctx (Inf ii) = iEval ctx ii
cEval ctx (Lam c ) = VLam (\x -> cEval (second (x :) ctx) c)
cEval _   Universe = VUniverse
cEval ctx (Pi p ty ty') =
  VPi p (cEval ctx ty) (\x -> cEval (second (x :) ctx) ty')
cEval ctx (MPair c c') = VMPair (cEval ctx c) (cEval ctx c')
cEval ctx (MPairType p ty ty') =
  VMPairType p (cEval ctx ty) (\x -> cEval (second (x :) ctx) ty')
cEval _   MUnit        = VMUnit
cEval _   MUnitType    = VMUnitType
cEval ctx (APair c c') = VAPair (cEval ctx c) (cEval ctx c')
cEval ctx (APairType ty ty') =
  VAPairType (cEval ctx ty) (\x -> cEval (second (x :) ctx) ty')
cEval _ AUnit     = VAUnit
cEval _ AUnitType = VAUnitType

-- | Evaluate a type-synthesising term in a given context.
--
-- Context is a pair in which first element contains values of global variables
-- and second element contains values of local variables.
iEval :: (ValueEnv, BoundEnv) -> ITerm -> Value
iEval ctx (Ann c _) = cEval ctx c
iEval ctx (Free x ) = case lookup x (fst ctx) of
  Nothing -> vfree x
  Just v  -> v
iEval ctx (Bound ii) = snd ctx !! ii
iEval ctx (i :$: c ) = case iEval ctx i of
  VLam     f -> f val
  VNeutral n -> VNeutral (NApp n val)
  v          -> error
    ("internal: Unable to apply " <> show v <> " to the value " <> show val)
  where val = cEval ctx c
iEval ctx (MPairElim i c c') = case iEval ctx i of
  VMPair x y -> cEval (second ([y, x] ++) ctx) c
  VNeutral n -> VNeutral $ NMPairElim
    n
    (\x y -> cEval (second ([y, x] ++) ctx) c)
    (\z -> cEval (second (z :) ctx) c')
  v -> error
    ("internal: Unable to eliminate " <> show v <> ", because it is not a pair")
iEval ctx (MUnitElim i c c') = case iEval ctx i of
  VMUnit -> cEval ctx c
  VNeutral n ->
    VNeutral $ NMUnitElim n (cEval ctx c) (\x -> cEval (second (x :) ctx) c')
  v -> error
    ("internal: Unable to eliminate " <> show v <> ", because it is not a unit")
iEval ctx (Fst i) = case iEval ctx i of
  VAPair x _ -> x
  VNeutral n -> VNeutral $ NFst n
  v          -> error
    ("internal: Unable to eliminate " <> show v <> ", because it is not a pair")
iEval ctx (Snd i) = case iEval ctx i of
  VAPair _ y -> y
  VNeutral n -> VNeutral $ NSnd n
  v          -> error
    ("internal: Unable to eliminate " <> show v <> ", because it is not a pair")

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

-- | Convert a value to a term.
--
-- This conversion is necessary because 'Value' uses higher-order abstract
-- syntax, i.e. Haskell functions, to represent data members, so to show or
-- equate them they are first converted to terms.
quote0 :: Value -> CTerm
quote0 = quote 0

quote :: Int -> Value -> CTerm
quote ii (VLam t)  = Lam (quote (ii + 1) (t . vfree $ Quote ii))
quote _  VUniverse = Universe
quote ii (VPi p v f) =
  Pi p (quote ii v) (quote (ii + 1) (f . vfree $ Quote ii))
quote ii (VNeutral n ) = Inf $ neutralQuote ii n
quote ii (VMPair v v') = MPair (quote ii v) (quote ii v')
quote ii (VMPairType p v f) =
  MPairType p (quote ii v) (quote (ii + 1) (f . vfree $ Quote ii))
quote _  VMUnit        = MUnit
quote _  VMUnitType    = MUnitType
quote ii (VAPair v v') = APair (quote ii v) (quote ii v')
quote ii (VAPairType v f) =
  APairType (quote ii v) (quote (ii + 1) (f . vfree $ Quote ii))
quote _ VAUnit     = AUnit
quote _ VAUnitType = AUnitType

neutralQuote :: Int -> Neutral -> ITerm
neutralQuote ii (NFree (Quote k)  ) = Bound ((ii - k - 1) `max` 0)
neutralQuote _  (NFree x          ) = Free x
neutralQuote ii (NApp n v         ) = neutralQuote ii n :$: quote ii v
neutralQuote ii (NMPairElim n v v') = MPairElim
  (neutralQuote ii n)
  (quote (ii + 2) $ v (vfree $ Quote ii) (vfree $ Quote (ii + 1)))
  (quote (ii + 1) (v' . vfree $ Quote ii))
neutralQuote ii (NMUnitElim n v v') = MUnitElim
  (neutralQuote ii n)
  (quote ii v)
  (quote (ii + 1) (v' . vfree $ Quote ii))
neutralQuote ii (NFst n) = Fst (neutralQuote ii n)
neutralQuote ii (NSnd n) = Snd (neutralQuote ii n)

