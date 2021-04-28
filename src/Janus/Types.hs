module Janus.Types
  ( Binding(..)
  , BoundEnv
  , Context
  , CTerm(..)
  , ITerm(..)
  , Name(..)
  , Neutral(..)
  , Result
  , Type
  , TypeEnv
  , TypeError(..)
  , Value(..)
  , ValueEnv
  , cEval
  , cSubst
  , iEval
  , iSubst
  , vfree
  , quote0
  ) where

import           Data.Bifunctor                 ( second )
import           Data.Text.Prettyprint.Doc      ( Doc )
import           Data.Text.Prettyprint.Doc.Render.Terminal
                                                ( AnsiStyle )
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

data TypeError
   =  UsageError (Maybe String) [(Name, Type, ZeroOneMany, ZeroOneMany)]
   |  ErasureError CTerm ZeroOneMany
   |  InferenceError (Doc AnsiStyle) Type ITerm
   |  CheckError Type CTerm
   |  UnknownVarError Name

type Result = Either TypeError
type Type = Value

type TypeEnv = [Binding Name ZeroOneMany Type]
type ValueEnv = [(Name, Value)]
type BoundEnv = [Value]
type Context = (ValueEnv, TypeEnv)

vfree :: Name -> Value
vfree n = VNeutral (NFree n)

cEval :: CTerm -> (ValueEnv, BoundEnv) -> Value
cEval (Inf ii)      d = iEval ii d
cEval (Lam c )      d = VLam (\x -> cEval c $ second (x :) d)
cEval Universe      _ = VUniverse
cEval (Pi p ty ty') d = VPi p (cEval ty d) (\x -> cEval ty' $ second (x :) d)
cEval (MPair c c' ) d = VMPair (cEval c d) (cEval c' d)
cEval (MPairType p ty ty') d =
  VMPairType p (cEval ty d) (\x -> cEval ty' $ second (x :) d)
cEval MUnit        _ = VMUnit
cEval MUnitType    _ = VMUnitType
cEval (APair c c') d = VAPair (cEval c d) (cEval c' d)
cEval (APairType ty ty') d =
  VAPairType (cEval ty d) (\x -> cEval ty' $ second (x :) d)
cEval AUnit     _ = VAUnit
cEval AUnitType _ = VAUnitType

iEval :: ITerm -> (ValueEnv, BoundEnv) -> Value
iEval (Ann c _) d = cEval c d
iEval (Free x ) d = case lookup x (fst d) of
  Nothing -> vfree x
  Just v  -> v
iEval (Bound ii) d = snd d !! ii
iEval (i :$: c ) d = case iEval i d of
  (VLam     f) -> f val
  (VNeutral n) -> VNeutral (NApp n val)
  v            -> error
    ("internal: Unable to apply " <> show v <> " to the value " <> show val)
  where val = cEval c d
iEval (MPairElim i c c') d = case iEval i d of
  (VMPair x y) -> cEval c (second ([y, x] ++) d)
  (VNeutral n) -> VNeutral $ NMPairElim
    n
    (\x y -> cEval c $ second ([y, x] ++) d)
    (\z -> cEval c' $ second (z :) d)
  v -> error
    ("internal: Unable to eliminate " <> show v <> ", because it is not a pair")
iEval (MUnitElim i c c') d = case iEval i d of
  VMUnit -> cEval c d
  (VNeutral n) ->
    VNeutral $ NMUnitElim n (cEval c d) (\x -> cEval c' $ second (x :) d)
  v -> error
    ("internal: Unable to eliminate " <> show v <> ", because it is not a unit")
iEval (Fst i) d = case iEval i d of
  (VAPair x _) -> x
  (VNeutral n) -> VNeutral $ NFst n
  v            -> error
    ("internal: Unable to eliminate " <> show v <> ", because it is not a pair")
iEval (Snd i) d = case iEval i d of
  (VAPair _ y) -> y
  (VNeutral n) -> VNeutral $ NSnd n
  v            -> error
    ("internal: Unable to eliminate " <> show v <> ", because it is not a pair")

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
neutralQuote ii (NFree v          ) = boundfree ii v
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

boundfree :: Int -> Name -> ITerm
boundfree ii (Quote k) = Bound ((ii - k - 1) `max` 0)
boundfree _  x         = Free x

