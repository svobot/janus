-- | Implements the algorithm for evaluation of terms and defines a data type
-- ('Value') for representing an evaluated term using a higher-order syntax.
module Janus.Evaluation
  ( Type
  , ValueEnv
  , Value
    ( VAPair
    , VAPairType
    , VAUnit
    , VAUnitType
    , VLam
    , VMPair
    , VMPairType
    , VMUnit
    , VMUnitType
    , VPi
    , VSumL
    , VSumR
    , VSumType
    , VUniverse
    )
  , cEval
  , iEval
  , vfree
  , quote0
  , -- * Utils
    BoundEnv
  ) where

import           Data.Bifunctor                 ( second )
import           Janus.Semiring
import           Janus.Syntax

-- | A term that has been beta-reduced to its normal form.
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
   |  VSumL Value
   |  VSumR Value
   |  VSumType Value Value

instance Show Value where
  show = show . quote0

-- | A term whose further beta-reduction depends on a variable.
data Neutral
   =  NFree Name
   |  NApp Neutral Value
   |  NMPairElim Neutral (Value -> Value -> Value) (Value -> Value)
   |  NMUnitElim Neutral Value (Value -> Value)
   |  NFst Neutral
   |  NSnd Neutral
   |  NSumElim ZeroOneMany Neutral (Value -> Value) (Value -> Value) (Value -> Value)

type Type = Value

-- | List of values defined by the /let/ statement.
type ValueEnv = [(Name, Value)]

-- | List of values of the bound variables that are in scope.
--
-- This is an implementation detail of the evaluation functions and should
-- always start off empty.
type BoundEnv = [Value]

-- | Creates the 'Value' corresponding to a free variable.
vfree :: Name -> Value
vfree = VNeutral . NFree

-- | Evaluate a type-checkable term in a given environment.
--
-- Environment is a pair in which first element contains values of global variables
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
cEval _   AUnit          = VAUnit
cEval _   AUnitType      = VAUnitType
cEval ctx (SumL c      ) = VSumL (cEval ctx c)
cEval ctx (SumR c      ) = VSumR (cEval ctx c)
cEval ctx (SumType c c') = VSumType (cEval ctx c) (cEval ctx c')

-- | Evaluate a type-synthesising term in a given environment.
--
-- Environment is a pair in which first element contains values of global variables
-- and second element contains values of local variables.
iEval :: (ValueEnv, BoundEnv) -> ITerm -> Value
iEval ctx (Ann c _) = cEval ctx c
iEval ctx (Free x ) = case lookup x (fst ctx) of
  Nothing -> vfree x
  Just v  -> v
iEval ctx (Bound ii) = snd ctx !! ii
iEval ctx (i :$: c ) = case iEval ctx i of
  VLam     f -> f val
  VNeutral n -> VNeutral $ NApp n val
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
iEval ctx (SumElim p i c c' c'') = case iEval ctx i of
  VSumL    x -> cEval (second (x :) ctx) c
  VSumR    y -> cEval (second (y :) ctx) c'
  VNeutral n -> VNeutral $ NSumElim p
                                    n
                                    (\x -> cEval (second (x :) ctx) c)
                                    (\y -> cEval (second (y :) ctx) c')
                                    (\z -> cEval (second (z :) ctx) c'')
  v -> error
    ("internal: Unable to eliminate " <> show v <> ", because it is not a sum")

-- | Convert a value to a term.
--
-- This conversion is necessary because 'Value' uses higher-order abstract
-- syntax, i.e. Haskell functions, to represent data members, so to show or
-- equate them they are first converted to terms.
quote0 :: Value -> CTerm
quote0 = quote 0

quote :: Int -> Value -> CTerm
quote ii (VLam t)      = Lam $ quote (ii + 1) (t $ quoteArg ii)
quote _  VUniverse     = Universe
quote ii (VPi p v f  ) = Pi p (quote ii v) $ quote (ii + 1) (f $ quoteArg ii)
quote ii (VNeutral n ) = Inf $ neutralQuote ii n
quote ii (VMPair v v') = MPair (quote ii v) (quote ii v')
quote ii (VMPairType p v f) =
  MPairType p (quote ii v) $ quote (ii + 1) (f $ quoteArg ii)
quote _  VMUnit        = MUnit
quote _  VMUnitType    = MUnitType
quote ii (VAPair v v') = APair (quote ii v) (quote ii v')
quote ii (VAPairType v f) =
  APairType (quote ii v) $ quote (ii + 1) (f $ quoteArg ii)
quote _  VAUnit          = AUnit
quote _  VAUnitType      = AUnitType
quote ii (VSumL v      ) = SumL $ quote ii v
quote ii (VSumR v      ) = SumR $ quote ii v
quote ii (VSumType v v') = SumType (quote ii v) (quote ii v')

neutralQuote :: Int -> Neutral -> ITerm
neutralQuote ii (NFree (Quote k)  ) = Bound $ (ii - k - 1) `max` 0
neutralQuote _  (NFree x          ) = Free x
neutralQuote ii (NApp n v         ) = neutralQuote ii n :$: quote ii v
neutralQuote ii (NMPairElim n v v') = MPairElim
  (neutralQuote ii n)
  (quote (ii + 2) $ v (quoteArg ii) (quoteArg $ ii + 1))
  (quote (ii + 1) (v' $ quoteArg ii))
neutralQuote ii (NMUnitElim n v v') =
  MUnitElim (neutralQuote ii n) (quote ii v) $ quote (ii + 1) (v' $ quoteArg ii)
neutralQuote ii (NFst n               ) = Fst $ neutralQuote ii n
neutralQuote ii (NSnd n               ) = Snd $ neutralQuote ii n
neutralQuote ii (NSumElim p n v v' v'') = SumElim
  p
  (neutralQuote ii n)
  (quote (ii + 1) $ v (quoteArg $ ii + 1))
  (quote (ii + 1) $ v' (quoteArg $ ii + 1))
  (quote (ii + 1) $ v'' (quoteArg $ ii + 1))

quoteArg :: Int -> Value
quoteArg = vfree . Quote
