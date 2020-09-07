module Types where

import           Control.Monad.State.Lazy       ( StateT )
import           Data.Bifunctor                 ( second )
import           System.Console.Repline

type Repl a = HaskelineT (StateT IState IO) a

data Name
   =  Global  String
   |  Local   Int
   |  Quote   Int
  deriving (Show, Eq, Ord)

data CTerm
   =  Inf  ITerm
   |  Lam  CTerm
   |  Star
   |  Pi ZeroOneOmega CTerm CTerm
  deriving (Show, Eq)

data ITerm
   =  Ann CTerm CTerm
   |  Bound Int
   |  Free Name
   |  ITerm :@: CTerm
  deriving (Show, Eq)

data Value
   =  VLam  (Value -> Value)
   |  VStar
   |  VPi ZeroOneOmega Value (Value -> Value)
   |  VNeutral Neutral

instance Show Value where
  show = show . quote0

data Neutral
   =  NFree  Name
   |  NApp  Neutral Value

type Result a = Either String a

data ZeroOneOmega = Rig0 | Rig1 | RigW deriving (Eq)

instance Show ZeroOneOmega where
  show Rig0 = "0"
  show Rig1 = "1"
  show RigW = "w"

rigPlus :: ZeroOneOmega -> ZeroOneOmega -> ZeroOneOmega
rigPlus Rig0 a    = a
rigPlus a    Rig0 = a
rigPlus Rig1 _    = RigW
rigPlus _    Rig1 = RigW
rigPlus RigW RigW = RigW

rigMult :: ZeroOneOmega -> ZeroOneOmega -> ZeroOneOmega
rigMult Rig0 _    = Rig0
rigMult _    Rig0 = Rig0
rigMult Rig1 a    = a
rigMult a    Rig1 = a
rigMult RigW RigW = RigW

rigLess :: ZeroOneOmega -> ZeroOneOmega -> Bool
rigLess Rig0 RigW = True
rigLess Rig1 RigW = True
rigLess x    y    = x == y

type Type = Value
type Env = [Value]
type Context = [(Name, (ZeroOneOmega, Type))]
type NameEnv = [(Name, Value)]
type IState = (Bool, String, NameEnv, Context)

vapp :: Value -> Value -> Value
vapp (VLam     f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

vfree :: Name -> Value
vfree n = VNeutral (NFree n)

cEval :: CTerm -> (NameEnv, Env) -> Value
cEval (Inf ii)      d = iEval ii d
cEval (Lam c )      d = VLam (\x -> cEval c $ second (x :) d)
cEval Star          _ = VStar
cEval (Pi p ty ty') d = VPi p (cEval ty d) (\x -> cEval ty' $ second (x :) d)

iEval :: ITerm -> (NameEnv, Env) -> Value
iEval (Ann c _) d = cEval c d
iEval (Free x ) d = case lookup x (fst d) of
  Nothing -> vfree x
  Just v  -> v
iEval (Bound ii) d = snd d !! ii
iEval (i :@: c ) d = vapp (iEval i d) (cEval c d)

iSubst :: Int -> ITerm -> ITerm -> ITerm
iSubst ii i' (Ann c c') = Ann (cSubst ii i' c) (cSubst ii i' c')
iSubst ii i' (Bound j ) = if ii == j then i' else Bound j
iSubst _  _  (Free  y ) = Free y
iSubst ii i' (i :@: c ) = iSubst ii i' i :@: cSubst ii i' c

cSubst :: Int -> ITerm -> CTerm -> CTerm
cSubst ii i' (Inf i)       = Inf (iSubst ii i' i)
cSubst ii i' (Lam c)       = Lam (cSubst (ii + 1) i' c)
cSubst _  _  Star          = Star
cSubst ii r  (Pi p ty ty') = Pi p (cSubst ii r ty) (cSubst (ii + 1) r ty')

quote0 :: Value -> CTerm
quote0 = quote 0

quote :: Int -> Value -> CTerm
quote ii (VLam t) = Lam (quote (ii + 1) (t . vfree $ Quote ii))
quote _  VStar    = Star
quote ii (VPi p v f) =
  Pi p (quote ii v) (quote (ii + 1) (f . vfree $ Quote ii))
quote ii (VNeutral n) = Inf (neutralQuote ii n)

neutralQuote :: Int -> Neutral -> ITerm
neutralQuote ii (NFree v ) = boundfree ii v
neutralQuote ii (NApp n v) = neutralQuote ii n :@: quote ii v

boundfree :: Int -> Name -> ITerm
boundfree ii (Quote k) = Bound ((ii - k - 1) `max` 0)
boundfree _  x         = Free x

forget :: Context -> Context
forget = map (\(n, (_, t)) -> (n, (Rig0, t)))

