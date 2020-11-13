module Types where

import           Control.Monad.State.Lazy       ( StateT )
import           Data.Bifunctor                 ( second )
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
   |  Star
   |  Pi ZeroOneMany CTerm CTerm
   |  Pair CTerm CTerm
   |  TensPr ZeroOneMany CTerm CTerm
   |  Unit
   |  UnitType
  deriving (Show, Eq)

data ITerm
   =  Ann CTerm CTerm
   |  Bound Int
   |  Free Name
   |  ITerm :@: CTerm
   |  PairElim ITerm CTerm CTerm
   |  UnitElim ITerm CTerm CTerm
  deriving (Show, Eq)

data Value
   =  VLam (Value -> Value)
   |  VStar
   |  VPi ZeroOneMany Value (Value -> Value)
   |  VNeutral Neutral
   |  VPair Value Value
   |  VTensPr ZeroOneMany Value (Value -> Value)
   |  VUnit
   |  VUnitType

instance Show Value where
  show = show . quote0

data Neutral
   =  NFree Name
   |  NApp Neutral Value
   |  NPairElim Neutral (Value -> Value -> Value) (Value -> Value)
   |  NUnitElim Neutral Value (Value -> Value)

data Binding s = Binding
  { bndName  :: Name
  , bndUsage :: s
  , bndType  :: Type
  }

instance Show s => Show (Binding s) where
  show (Binding n u t) = show u <> " " <> show n <> " : " <> show t

type Result a = Either String a
type Type = Value
type Context = [Binding ZeroOneMany]
type NameEnv = [(Name, Value)]
type Env = [Value]

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
cEval (Pair c c'  ) d = VPair (cEval c d) (cEval c' d)
cEval (TensPr p ty ty') d =
  VTensPr p (cEval ty d) (\x -> cEval ty' $ second (x :) d)
cEval Unit     _ = VUnit
cEval UnitType _ = VUnitType

iEval :: ITerm -> (NameEnv, Env) -> Value
iEval (Ann c _) d = cEval c d
iEval (Free x ) d = case lookup x (fst d) of
  Nothing -> vfree x
  Just v  -> v
iEval (Bound ii       ) d = snd d !! ii
iEval (i :@: c        ) d = vapp (iEval i d) (cEval c d)
iEval (PairElim i c c') d = case iEval i d of
  (VPair x y ) -> cEval c (second ([y, x] ++) d)
  (VNeutral n) -> VNeutral $ NPairElim
    n
    (\x y -> cEval c $ second ([y, x] ++) d)
    (\z -> cEval c' $ second (z :) d)
  _ -> error "internal" -- TODO: Fail gracefully?
iEval (UnitElim i c c') d = case iEval i d of
  VUnit -> cEval c (second (VUnit :) d)
  (VNeutral n) ->
    VNeutral $ NUnitElim n (cEval c d) (\x -> cEval c' $ second (x :) d)
  _ -> error "internal" -- TODO: Fail gracefully?

iSubst :: Int -> ITerm -> ITerm -> ITerm
iSubst ii i' (Ann c c') = Ann (cSubst ii i' c) (cSubst ii i' c')
iSubst ii i' (Bound j ) = if ii == j then i' else Bound j
iSubst _  _  (Free  y ) = Free y
iSubst ii i' (i :@: c ) = iSubst ii i' i :@: cSubst ii i' c
iSubst ii r (PairElim i c c') =
  PairElim (iSubst ii r i) (cSubst (ii + 2) r c) (cSubst (ii + 1) r c')
iSubst ii r (UnitElim i c c') =
  UnitElim (iSubst ii r i) (cSubst ii r c) (cSubst (ii + 1) r c')

cSubst :: Int -> ITerm -> CTerm -> CTerm
cSubst ii i' (Inf i)       = Inf (iSubst ii i' i)
cSubst ii i' (Lam c)       = Lam (cSubst (ii + 1) i' c)
cSubst _  _  Star          = Star
cSubst ii r  (Pi p ty ty') = Pi p (cSubst ii r ty) (cSubst (ii + 1) r ty')
cSubst ii r  (Pair c c'  ) = Pair (cSubst ii r c) (cSubst ii r c')
cSubst ii r (TensPr p ty ty') =
  TensPr p (cSubst ii r ty) (cSubst (ii + 1) r ty')
cSubst _ _ Unit     = Unit
cSubst _ _ UnitType = UnitType

quote0 :: Value -> CTerm
quote0 = quote 0

quote :: Int -> Value -> CTerm
quote ii (VLam t) = Lam (quote (ii + 1) (t . vfree $ Quote ii))
quote _  VStar    = Star
quote ii (VPi p v f) =
  Pi p (quote ii v) (quote (ii + 1) (f . vfree $ Quote ii))
quote ii (VNeutral n) = Inf $ neutralQuote ii n
quote ii (VPair v v') = Pair (quote ii v) (quote ii v')
quote ii (VTensPr p v f) =
  TensPr p (quote ii v) (quote (ii + 1) (f . vfree $ Quote ii))
quote _ VUnit     = Unit
quote _ VUnitType = UnitType

neutralQuote :: Int -> Neutral -> ITerm
neutralQuote ii (NFree v         ) = boundfree ii v
neutralQuote ii (NApp n v        ) = neutralQuote ii n :@: quote ii v
neutralQuote ii (NPairElim n v v') = PairElim
  (neutralQuote ii n)
  (quote (ii + 2) $ v (vfree $ Quote ii) (vfree $ Quote (ii + 1)))
  (quote (ii + 1) (v' . vfree $ Quote ii))
neutralQuote ii (NUnitElim n v v') = UnitElim
  (neutralQuote ii n)
  (quote ii v)
  (quote (ii + 1) (v' . vfree $ Quote ii))

boundfree :: Int -> Name -> ITerm
boundfree ii (Quote k) = Bound ((ii - k - 1) `max` 0)
boundfree _  x         = Free x

forget :: Context -> Context
forget = map (\b -> b { bndUsage = Zero })

