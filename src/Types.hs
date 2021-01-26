module Types where

import           Control.Monad.State            ( StateT )
import           Data.Bifunctor                 ( second )
import           Data.Text.Prettyprint.Doc      ( Doc )
import           Data.Text.Prettyprint.Doc.Render.Terminal
                                                ( AnsiStyle )
import           Rig
import           System.Console.Repline         ( HaskelineT )

type Repl a = HaskelineT (StateT IState IO) a
type IState = (Bool, String, NameEnv, Context)

data Name
   =  Global String
   |  Local Int
   |  Quote Int
  deriving (Show, Eq, Ord)

data CTerm
   =  Inf ITerm
   |  Lam CTerm
   |  Universe
   |  Pi ZeroOneMany CTerm CTerm
   |  Pair CTerm CTerm
   |  Tensor ZeroOneMany CTerm CTerm
   |  MUnit
   |  MUnitType
   |  Angles CTerm CTerm
   |  With CTerm CTerm
   |  AUnit
   |  AUnitType
  deriving (Show, Eq)

data ITerm
   =  Ann CTerm CTerm
   |  Bound Int
   |  Free Name
   |  ITerm :$: CTerm
   |  PairElim ITerm CTerm CTerm
   |  MUnitElim ITerm CTerm CTerm
   |  Fst ITerm
   |  Snd ITerm
  deriving (Show, Eq)

data Value
   =  VLam (Value -> Value)
   |  VUniverse
   |  VPi ZeroOneMany Value (Value -> Value)
   |  VNeutral Neutral
   |  VPair Value Value
   |  VTensor ZeroOneMany Value (Value -> Value)
   |  VMUnit
   |  VMUnitType
   |  VAngles Value Value
   |  VWith Value (Value -> Value)
   |  VAUnit
   |  VAUnitType

instance Show Value where
  show = show . quote0

data Neutral
   =  NFree Name
   |  NApp Neutral Value
   |  NPairElim Neutral (Value -> Value -> Value) (Value -> Value)
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
   =  MultiplicityError (Maybe String) [(Name, Type, ZeroOneMany, ZeroOneMany)]
   |  WrongInference (Doc AnsiStyle) Type ITerm
   |  WrongCheck Type CTerm
   |  UnknownVar Name

type Result a = Either TypeError a
type Type = Value
type Context = [Binding Name ZeroOneMany Type]
type NameEnv = [(Name, Value)]
type Env = [Value]

vapp :: Value -> Value -> Value
vapp (VLam     f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)
vapp v v' =
  error ("internal: Unable to apply " <> show v <> " to the value " <> show v')

vfree :: Name -> Value
vfree n = VNeutral (NFree n)

cEval :: CTerm -> (NameEnv, Env) -> Value
cEval (Inf ii)      d = iEval ii d
cEval (Lam c )      d = VLam (\x -> cEval c $ second (x :) d)
cEval Universe      _ = VUniverse
cEval (Pi p ty ty') d = VPi p (cEval ty d) (\x -> cEval ty' $ second (x :) d)
cEval (Pair c c'  ) d = VPair (cEval c d) (cEval c' d)
cEval (Tensor p ty ty') d =
  VTensor p (cEval ty d) (\x -> cEval ty' $ second (x :) d)
cEval MUnit           _ = VMUnit
cEval MUnitType       _ = VMUnitType
cEval (Angles c  c' ) d = VAngles (cEval c d) (cEval c' d)
cEval (With   ty ty') d = VWith (cEval ty d) (\x -> cEval ty' $ second (x :) d)
cEval AUnit           _ = VAUnit
cEval AUnitType       _ = VAUnitType

iEval :: ITerm -> (NameEnv, Env) -> Value
iEval (Ann c _) d = cEval c d
iEval (Free x ) d = case lookup x (fst d) of
  Nothing -> vfree x
  Just v  -> v
iEval (Bound ii       ) d = snd d !! ii
iEval (i :$: c        ) d = vapp (iEval i d) (cEval c d)
iEval (PairElim i c c') d = case iEval i d of
  (VPair x y ) -> cEval c (second ([y, x] ++) d)
  (VNeutral n) -> VNeutral $ NPairElim
    n
    (\x y -> cEval c $ second ([y, x] ++) d)
    (\z -> cEval c' $ second (z :) d)
  v -> error
    ("internal: Unable to eliminate " <> show v <> ", because it is not a pair")
iEval (MUnitElim i c c') d = case iEval i d of
  VMUnit -> cEval c (second (VMUnit :) d)
  (VNeutral n) ->
    VNeutral $ NMUnitElim n (cEval c d) (\x -> cEval c' $ second (x :) d)
  v -> error
    ("internal: Unable to eliminate " <> show v <> ", because it is not a unit")
iEval (Fst i) d = case iEval i d of
  (VAngles x _) -> x
  (VNeutral n ) -> VNeutral $ NFst n
  v             -> error
    ("internal: Unable to eliminate " <> show v <> ", because it is not a pair")
iEval (Snd i) d = case iEval i d of
  (VAngles _ y) -> y
  (VNeutral n ) -> VNeutral $ NSnd n
  v             -> error
    ("internal: Unable to eliminate " <> show v <> ", because it is not a pair")

iSubst :: Int -> ITerm -> ITerm -> ITerm
iSubst ii i' (Ann c c') = Ann (cSubst ii i' c) (cSubst ii i' c')
iSubst ii i' (Bound j ) = if ii == j then i' else Bound j
iSubst _  _  (Free  y ) = Free y
iSubst ii i' (i :$: c ) = iSubst ii i' i :$: cSubst ii i' c
iSubst ii r (PairElim i c c') =
  PairElim (iSubst ii r i) (cSubst (ii + 2) r c) (cSubst (ii + 1) r c')
iSubst ii r (MUnitElim i c c') =
  MUnitElim (iSubst ii r i) (cSubst ii r c) (cSubst (ii + 1) r c')
iSubst ii r (Fst i) = Fst (iSubst ii r i)
iSubst ii r (Snd i) = Snd (iSubst ii r i)

cSubst :: Int -> ITerm -> CTerm -> CTerm
cSubst ii i' (Inf i)       = Inf (iSubst ii i' i)
cSubst ii i' (Lam c)       = Lam (cSubst (ii + 1) i' c)
cSubst _  _  Universe      = Universe
cSubst ii r  (Pi p ty ty') = Pi p (cSubst ii r ty) (cSubst (ii + 1) r ty')
cSubst ii r  (Pair c c'  ) = Pair (cSubst ii r c) (cSubst ii r c')
cSubst ii r (Tensor p ty ty') =
  Tensor p (cSubst ii r ty) (cSubst (ii + 1) r ty')
cSubst _  _ MUnit           = MUnit
cSubst _  _ MUnitType       = MUnitType
cSubst ii r (Angles c  c' ) = Angles (cSubst ii r c) (cSubst ii r c')
cSubst ii r (With   ty ty') = With (cSubst ii r ty) (cSubst (ii + 1) r ty')
cSubst _  _ AUnit           = AUnit
cSubst _  _ AUnitType       = AUnitType

quote0 :: Value -> CTerm
quote0 = quote 0

quote :: Int -> Value -> CTerm
quote ii (VLam t)  = Lam (quote (ii + 1) (t . vfree $ Quote ii))
quote _  VUniverse = Universe
quote ii (VPi p v f) =
  Pi p (quote ii v) (quote (ii + 1) (f . vfree $ Quote ii))
quote ii (VNeutral n) = Inf $ neutralQuote ii n
quote ii (VPair v v') = Pair (quote ii v) (quote ii v')
quote ii (VTensor p v f) =
  Tensor p (quote ii v) (quote (ii + 1) (f . vfree $ Quote ii))
quote _  VMUnit         = MUnit
quote _  VMUnitType     = MUnitType
quote ii (VAngles v v') = Angles (quote ii v) (quote ii v')
quote ii (VWith v f) =
  With (quote ii v) (quote (ii + 1) (f . vfree $ Quote ii))
quote _ VAUnit     = AUnit
quote _ VAUnitType = AUnitType

neutralQuote :: Int -> Neutral -> ITerm
neutralQuote ii (NFree v         ) = boundfree ii v
neutralQuote ii (NApp n v        ) = neutralQuote ii n :$: quote ii v
neutralQuote ii (NPairElim n v v') = PairElim
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

forget :: Context -> Context
forget = map (\b -> b { bndUsage = Zero })

