module Types where

import           Control.Monad.State.Lazy       ( StateT )
import           Data.Bifunctor                 ( second )
import           System.Console.Repline

type Repl a = HaskelineT (StateT (State Value Value) IO) a

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
  show = show . quote0_

data Neutral
   =  NFree  Name
   |  NApp  Neutral Value
   |  NNatElim Value Value Value Neutral
   |  NVecElim Value Value Value Value Value Neutral
   |  NEqElim Value Value Value Value Value Neutral
   |  NFinElim Value Value Value Value Neutral

type Result a = Either String a

type NameEnv v = [(Name, v)]
type Ctx inf = [(Name, inf)]
type State v inf = (Bool, String, NameEnv v, Ctx inf)

type Type = Value
type Context = [(Name, Type)]
type Env = [Value]

vapp_ :: Value -> Value -> Value
vapp_ (VLam     f) v = f v
vapp_ (VNeutral n) v = VNeutral (NApp n v)

vfree_ :: Name -> Value
vfree_ n = VNeutral (NFree n)

cEval_ :: CTerm -> (NameEnv Value, Env) -> Value
cEval_ (Inf ii) d = iEval_ ii d
cEval_ (Lam c ) d = VLam (\x -> cEval_ c (second ((:) x) d))
cEval_ Zero     _ = VZero
cEval_ (Succ k) d = VSucc (cEval_ k d)
cEval_ (Nil  a) d = VNil (cEval_ a d)
cEval_ (Cons a n x xs) d =
  VCons (cEval_ a d) (cEval_ n d) (cEval_ x d) (cEval_ xs d)
cEval_ (Refl a x ) d = VRefl (cEval_ a d) (cEval_ x d)
cEval_ (FZero n  ) d = VFZero (cEval_ n d)
cEval_ (FSucc n f) d = VFSucc (cEval_ n d) (cEval_ f d)

iEval_ :: ITerm -> (NameEnv Value, Env) -> Value
iEval_ (Ann c _)   d = cEval_ c d
iEval_ Star        _ = VStar
iEval_ (Pi ty ty') d = VPi (cEval_ ty d) (\x -> cEval_ ty' (second ((:) x) d))
iEval_ (Free x   ) d = case lookup x (fst d) of
  Nothing -> vfree_ x
  Just v  -> v
iEval_ (Bound ii) d = snd d !! ii
iEval_ (i :@: c ) d = vapp_ (iEval_ i d) (cEval_ c d)
iEval_ Nat        _ = VNat
iEval_ (NatElim m mz ms n) d =
  let mzVal = cEval_ mz d
      msVal = cEval_ ms d
      rec nVal = case nVal of
        VZero      -> mzVal
        VSucc    k -> msVal `vapp_` k `vapp_` rec k
        VNeutral n -> VNeutral (NNatElim (cEval_ m d) mzVal msVal n)
        _          -> error "internal: eval natElim"
  in  rec (cEval_ n d)
iEval_ (Vec a n) d = VVec (cEval_ a d) (cEval_ n d)
iEval_ (VecElim a m mn mc n xs) d =
  let
    mnVal = cEval_ mn d
    mcVal = cEval_ mc d
    rec nVal xsVal = case xsVal of
      VNil _         -> mnVal
      VCons _ k x xs -> foldl vapp_ mcVal [k, x, xs, rec k xs]
      VNeutral n ->
        VNeutral (NVecElim (cEval_ a d) (cEval_ m d) mnVal mcVal nVal n)
      _ -> error "internal: eval vecElim"
  in
    rec (cEval_ n d) (cEval_ xs d)
iEval_ (Eq a x y) d = VEq (cEval_ a d) (cEval_ x d) (cEval_ y d)
iEval_ (EqElim a m mr x y eq) d =
  let mrVal = cEval_ mr d
      rec eqVal = case eqVal of
        VRefl _ z -> mrVal `vapp_` z
        VNeutral n ->
          VNeutral
            (NEqElim (cEval_ a d) (cEval_ m d) mrVal (cEval_ x d) (cEval_ y d) n
            )
        _ -> error "internal: eval eqElim"
  in  rec (cEval_ eq d)
iEval_ (Fin n) d = VFin (cEval_ n d)
iEval_ (FinElim m mz ms n f) d =
  let
    mzVal = cEval_ mz d
    msVal = cEval_ ms d
    rec fVal = case fVal of
      VFZero k    -> mzVal `vapp_` k
      VFSucc k g  -> foldl vapp_ msVal [k, g, rec g]
      VNeutral n' -> VNeutral
        (NFinElim (cEval_ m d) (cEval_ mz d) (cEval_ ms d) (cEval_ n d) n')
      _ -> error "internal: eval finElim"
  in
    rec (cEval_ f d)

iSubst_ :: Int -> ITerm -> ITerm -> ITerm
iSubst_ ii i' (Ann c c')  = Ann (cSubst_ ii i' c) (cSubst_ ii i' c')
iSubst_ _  _  Star        = Star
iSubst_ ii r  (Pi ty ty') = Pi (cSubst_ ii r ty) (cSubst_ (ii + 1) r ty')
iSubst_ ii i' (Bound j  ) = if ii == j then i' else Bound j
iSubst_ _  _  (Free  y  ) = Free y
iSubst_ ii i' (i :@: c  ) = iSubst_ ii i' i :@: cSubst_ ii i' c
iSubst_ _  _  Nat         = Nat
iSubst_ ii r (NatElim m mz ms _) =
  NatElim (cSubst_ ii r m) (cSubst_ ii r mz) (cSubst_ ii r ms) (cSubst_ ii r ms)
iSubst_ ii r (Vec a n               ) = Vec (cSubst_ ii r a) (cSubst_ ii r n)
iSubst_ ii r (VecElim a m mn mc n xs) = VecElim (cSubst_ ii r a)
                                                (cSubst_ ii r m)
                                                (cSubst_ ii r mn)
                                                (cSubst_ ii r mc)
                                                (cSubst_ ii r n)
                                                (cSubst_ ii r xs)
iSubst_ ii r (Eq a x y) = Eq (cSubst_ ii r a) (cSubst_ ii r x) (cSubst_ ii r y)
iSubst_ ii r (EqElim a m mr x y eq) = VecElim (cSubst_ ii r a)
                                              (cSubst_ ii r m)
                                              (cSubst_ ii r mr)
                                              (cSubst_ ii r x)
                                              (cSubst_ ii r y)
                                              (cSubst_ ii r eq)
iSubst_ ii r (Fin n              ) = Fin (cSubst_ ii r n)
iSubst_ ii r (FinElim m mz ms n f) = FinElim (cSubst_ ii r m)
                                             (cSubst_ ii r mz)
                                             (cSubst_ ii r ms)
                                             (cSubst_ ii r n)
                                             (cSubst_ ii r f)

cSubst_ :: Int -> ITerm -> CTerm -> CTerm
cSubst_ ii i' (Inf i)  = Inf (iSubst_ ii i' i)
cSubst_ ii i' (Lam c)  = Lam (cSubst_ (ii + 1) i' c)
cSubst_ _  _  Zero     = Zero
cSubst_ ii r  (Succ n) = Succ (cSubst_ ii r n)
cSubst_ ii r  (Nil  a) = Nil (cSubst_ ii r a)
cSubst_ ii r (Cons a _ x xs) =
  Cons (cSubst_ ii r a) (cSubst_ ii r x) (cSubst_ ii r x) (cSubst_ ii r xs)
cSubst_ ii r (Refl a x ) = Refl (cSubst_ ii r a) (cSubst_ ii r x)
cSubst_ ii r (FZero n  ) = FZero (cSubst_ ii r n)
cSubst_ ii r (FSucc n k) = FSucc (cSubst_ ii r n) (cSubst_ ii r k)

quote0_ :: Value -> CTerm
quote0_ = quote_ 0

quote_ :: Int -> Value -> CTerm
quote_ ii (VLam t) = Lam (quote_ (ii + 1) (t (vfree_ (Quote ii))))
quote_ _  VStar    = Inf Star
quote_ ii (VPi v f) =
  Inf (Pi (quote_ ii v) (quote_ (ii + 1) (f (vfree_ (Quote ii)))))
quote_ ii (VNeutral n) = Inf (neutralQuote_ ii n)
quote_ _  VNat         = Inf Nat
quote_ _  VZero        = Zero
quote_ ii (VSucc n )   = Succ (quote_ ii n)
quote_ ii (VVec a n)   = Inf (Vec (quote_ ii a) (quote_ ii n))
quote_ ii (VNil a  )   = Nil (quote_ ii a)
quote_ ii (VCons a n x xs) =
  Cons (quote_ ii a) (quote_ ii n) (quote_ ii x) (quote_ ii xs)
quote_ ii (VEq a x y ) = Inf (Eq (quote_ ii a) (quote_ ii x) (quote_ ii y))
quote_ ii (VRefl a x ) = Refl (quote_ ii a) (quote_ ii x)
quote_ ii (VFin   n  ) = Inf (Fin (quote_ ii n))
quote_ ii (VFZero n  ) = FZero (quote_ ii n)
quote_ ii (VFSucc n f) = FSucc (quote_ ii n) (quote_ ii f)

neutralQuote_ :: Int -> Neutral -> ITerm
neutralQuote_ ii (NFree v ) = boundfree_ ii v
neutralQuote_ ii (NApp n v) = neutralQuote_ ii n :@: quote_ ii v
neutralQuote_ ii (NNatElim m z s n) =
  NatElim (quote_ ii m) (quote_ ii z) (quote_ ii s) (Inf (neutralQuote_ ii n))
neutralQuote_ ii (NVecElim a m mn mc n xs) = VecElim
  (quote_ ii a)
  (quote_ ii m)
  (quote_ ii mn)
  (quote_ ii mc)
  (quote_ ii n)
  (Inf (neutralQuote_ ii xs))
neutralQuote_ ii (NEqElim a m mr x y eq) = EqElim (quote_ ii a)
                                                  (quote_ ii m)
                                                  (quote_ ii mr)
                                                  (quote_ ii x)
                                                  (quote_ ii y)
                                                  (Inf (neutralQuote_ ii eq))
neutralQuote_ ii (NFinElim m mz ms n f) = FinElim (quote_ ii m)
                                                  (quote_ ii mz)
                                                  (quote_ ii ms)
                                                  (quote_ ii n)
                                                  (Inf (neutralQuote_ ii f))

boundfree_ :: Int -> Name -> ITerm
boundfree_ ii (Quote k) = Bound ((ii - k - 1) `max` 0)
boundfree_ _  x         = Free x
