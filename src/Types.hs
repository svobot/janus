module Types where

import           Control.Monad.State.Lazy       ( StateT )
import           Data.Bifunctor                 ( second )
import           System.Console.Repline

type Repl a = HaskelineT (StateT IState IO) a

data Name
   =  Global  String
   |  Local   Int
   |  Quote   Int
  deriving (Show, Eq)

data CTerm
   =  Inf  ITerm
   |  Lam  CTerm
   |  Zero
   |  Succ CTerm
   |  Nil CTerm
   |  Cons CTerm CTerm CTerm CTerm
   |  Refl CTerm CTerm
   |  FZero CTerm
   |  FSucc CTerm CTerm
  deriving (Show, Eq)

data ITerm
   =  Ann CTerm CTerm
   |  Star
   |  Pi CTerm CTerm
   |  Bound  Int
   |  Free  Name
   |  ITerm :@: CTerm
   |  Nat
   |  NatElim CTerm CTerm CTerm CTerm
   |  Vec CTerm CTerm
   |  VecElim CTerm CTerm CTerm CTerm CTerm CTerm
   |  Eq CTerm CTerm CTerm
   |  EqElim CTerm CTerm CTerm CTerm CTerm CTerm
   |  Fin CTerm
   |  FinElim CTerm CTerm CTerm CTerm CTerm
  deriving (Show, Eq)

data Value
   =  VLam  (Value -> Value)
   |  VStar
   |  VPi Value (Value -> Value)
   |  VNeutral Neutral
   |  VNat
   |  VZero
   |  VSucc Value
   |  VNil Value
   |  VCons Value Value Value Value
   |  VVec Value Value
   |  VEq Value Value Value
   |  VRefl Value Value
   |  VFZero Value
   |  VFSucc Value Value
   |  VFin Value

instance Show Value where
  show = show . quote0

data Neutral
   =  NFree  Name
   |  NApp  Neutral Value
   |  NNatElim Value Value Value Neutral
   |  NVecElim Value Value Value Value Value Neutral
   |  NEqElim Value Value Value Value Value Neutral
   |  NFinElim Value Value Value Value Neutral

type Result a = Either String a

type Type = Value
type Env = [Value]
type Context = [(Name, Type)]
type NameEnv = [(Name, Value)]
type IState = (Bool, String, NameEnv, Context)

vapp :: Value -> Value -> Value
vapp (VLam     f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

vfree :: Name -> Value
vfree n = VNeutral (NFree n)

cEval :: CTerm -> (NameEnv, Env) -> Value
cEval (Inf ii) d = iEval ii d
cEval (Lam c ) d = VLam (\x -> cEval c (second ((:) x) d))
cEval Zero     _ = VZero
cEval (Succ k) d = VSucc (cEval k d)
cEval (Nil  a) d = VNil (cEval a d)
cEval (Cons a n x xs) d =
  VCons (cEval a d) (cEval n d) (cEval x d) (cEval xs d)
cEval (Refl a x ) d = VRefl (cEval a d) (cEval x d)
cEval (FZero n  ) d = VFZero (cEval n d)
cEval (FSucc n f) d = VFSucc (cEval n d) (cEval f d)

iEval :: ITerm -> (NameEnv, Env) -> Value
iEval (Ann c _)   d = cEval c d
iEval Star        _ = VStar
iEval (Pi ty ty') d = VPi (cEval ty d) (\x -> cEval ty' (second ((:) x) d))
iEval (Free x   ) d = case lookup x (fst d) of
  Nothing -> vfree x
  Just v  -> v
iEval (Bound ii) d = snd d !! ii
iEval (i :@: c ) d = vapp (iEval i d) (cEval c d)
iEval Nat        _ = VNat
iEval (NatElim m mz ms n) d =
  let mzVal = cEval mz d
      msVal = cEval ms d
      rec nVal = case nVal of
        VZero      -> mzVal
        VSucc    k -> msVal `vapp` k `vapp` rec k
        VNeutral n -> VNeutral (NNatElim (cEval m d) mzVal msVal n)
        _          -> error "internal: eval natElim"
  in  rec (cEval n d)
iEval (Vec a n) d = VVec (cEval a d) (cEval n d)
iEval (VecElim a m mn mc n xs) d =
  let
    mnVal = cEval mn d
    mcVal = cEval mc d
    rec nVal xsVal = case xsVal of
      VNil _         -> mnVal
      VCons _ k x xs -> foldl vapp mcVal [k, x, xs, rec k xs]
      VNeutral n ->
        VNeutral (NVecElim (cEval a d) (cEval m d) mnVal mcVal nVal n)
      _ -> error "internal: eval vecElim"
  in
    rec (cEval n d) (cEval xs d)
iEval (Eq a x y) d = VEq (cEval a d) (cEval x d) (cEval y d)
iEval (EqElim a m mr x y eq) d =
  let mrVal = cEval mr d
      rec eqVal = case eqVal of
        VRefl _ z  -> mrVal `vapp` z
        VNeutral n -> VNeutral
          (NEqElim (cEval a d) (cEval m d) mrVal (cEval x d) (cEval y d) n)
        _ -> error "internal: eval eqElim"
  in  rec (cEval eq d)
iEval (Fin n) d = VFin (cEval n d)
iEval (FinElim m mz ms n f) d =
  let
    mzVal = cEval mz d
    msVal = cEval ms d
    rec fVal = case fVal of
      VFZero k   -> mzVal `vapp` k
      VFSucc k g -> foldl vapp msVal [k, g, rec g]
      VNeutral n' ->
        VNeutral (NFinElim (cEval m d) (cEval mz d) (cEval ms d) (cEval n d) n')
      _ -> error "internal: eval finElim"
  in
    rec (cEval f d)

iSubst :: Int -> ITerm -> ITerm -> ITerm
iSubst ii i' (Ann c c')  = Ann (cSubst ii i' c) (cSubst ii i' c')
iSubst _  _  Star        = Star
iSubst ii r  (Pi ty ty') = Pi (cSubst ii r ty) (cSubst (ii + 1) r ty')
iSubst ii i' (Bound j  ) = if ii == j then i' else Bound j
iSubst _  _  (Free  y  ) = Free y
iSubst ii i' (i :@: c  ) = iSubst ii i' i :@: cSubst ii i' c
iSubst _  _  Nat         = Nat
iSubst ii r (NatElim m mz ms _) =
  NatElim (cSubst ii r m) (cSubst ii r mz) (cSubst ii r ms) (cSubst ii r ms)
iSubst ii r (Vec a n               ) = Vec (cSubst ii r a) (cSubst ii r n)
iSubst ii r (VecElim a m mn mc n xs) = VecElim (cSubst ii r a)
                                               (cSubst ii r m)
                                               (cSubst ii r mn)
                                               (cSubst ii r mc)
                                               (cSubst ii r n)
                                               (cSubst ii r xs)
iSubst ii r (Eq a x y) = Eq (cSubst ii r a) (cSubst ii r x) (cSubst ii r y)
iSubst ii r (EqElim a m mr x y eq) = VecElim (cSubst ii r a)
                                             (cSubst ii r m)
                                             (cSubst ii r mr)
                                             (cSubst ii r x)
                                             (cSubst ii r y)
                                             (cSubst ii r eq)
iSubst ii r (Fin n              ) = Fin (cSubst ii r n)
iSubst ii r (FinElim m mz ms n f) = FinElim (cSubst ii r m)
                                            (cSubst ii r mz)
                                            (cSubst ii r ms)
                                            (cSubst ii r n)
                                            (cSubst ii r f)

cSubst :: Int -> ITerm -> CTerm -> CTerm
cSubst ii i' (Inf i)  = Inf (iSubst ii i' i)
cSubst ii i' (Lam c)  = Lam (cSubst (ii + 1) i' c)
cSubst _  _  Zero     = Zero
cSubst ii r  (Succ n) = Succ (cSubst ii r n)
cSubst ii r  (Nil  a) = Nil (cSubst ii r a)
cSubst ii r (Cons a _ x xs) =
  Cons (cSubst ii r a) (cSubst ii r x) (cSubst ii r x) (cSubst ii r xs)
cSubst ii r (Refl a x ) = Refl (cSubst ii r a) (cSubst ii r x)
cSubst ii r (FZero n  ) = FZero (cSubst ii r n)
cSubst ii r (FSucc n k) = FSucc (cSubst ii r n) (cSubst ii r k)

quote0 :: Value -> CTerm
quote0 = quote 0

quote :: Int -> Value -> CTerm
quote ii (VLam t) = Lam (quote (ii + 1) (t (vfree (Quote ii))))
quote _  VStar    = Inf Star
quote ii (VPi v f) =
  Inf (Pi (quote ii v) (quote (ii + 1) (f (vfree (Quote ii)))))
quote ii (VNeutral n) = Inf (neutralQuote ii n)
quote _  VNat         = Inf Nat
quote _  VZero        = Zero
quote ii (VSucc n )   = Succ (quote ii n)
quote ii (VVec a n)   = Inf (Vec (quote ii a) (quote ii n))
quote ii (VNil a  )   = Nil (quote ii a)
quote ii (VCons a n x xs) =
  Cons (quote ii a) (quote ii n) (quote ii x) (quote ii xs)
quote ii (VEq a x y ) = Inf (Eq (quote ii a) (quote ii x) (quote ii y))
quote ii (VRefl a x ) = Refl (quote ii a) (quote ii x)
quote ii (VFin   n  ) = Inf (Fin (quote ii n))
quote ii (VFZero n  ) = FZero (quote ii n)
quote ii (VFSucc n f) = FSucc (quote ii n) (quote ii f)

neutralQuote :: Int -> Neutral -> ITerm
neutralQuote ii (NFree v ) = boundfree ii v
neutralQuote ii (NApp n v) = neutralQuote ii n :@: quote ii v
neutralQuote ii (NNatElim m z s n) =
  NatElim (quote ii m) (quote ii z) (quote ii s) (Inf (neutralQuote ii n))
neutralQuote ii (NVecElim a m mn mc n xs) = VecElim
  (quote ii a)
  (quote ii m)
  (quote ii mn)
  (quote ii mc)
  (quote ii n)
  (Inf (neutralQuote ii xs))
neutralQuote ii (NEqElim a m mr x y eq) = EqElim (quote ii a)
                                                 (quote ii m)
                                                 (quote ii mr)
                                                 (quote ii x)
                                                 (quote ii y)
                                                 (Inf (neutralQuote ii eq))
neutralQuote ii (NFinElim m mz ms n f) = FinElim (quote ii m)
                                                 (quote ii mz)
                                                 (quote ii ms)
                                                 (quote ii n)
                                                 (Inf (neutralQuote ii f))

boundfree :: Int -> Name -> ITerm
boundfree ii (Quote k) = Bound ((ii - k - 1) `max` 0)
boundfree _  x         = Free x
