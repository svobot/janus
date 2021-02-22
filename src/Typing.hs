{-# LANGUAGE TupleSections #-}

module Typing where

import           Control.Monad.Except           ( throwError )
import           Control.Monad.Reader           ( MonadIO(liftIO)
                                                , MonadReader(local)
                                                , ReaderT(runReaderT)
                                                , asks
                                                , unless
                                                )
import           Data.Bifunctor                 ( first
                                                , second
                                                )
import           Data.List                      ( find )
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( fromMaybe )
import qualified Data.Semiring                 as S
import qualified Data.Text.IO                  as T
import           Printer
import           Rig
import           Types

type Usage = Map.Map Name ZeroOneMany
type Judgement = ReaderT Context Result

iinfer :: Context -> ZeroOneMany -> ITerm -> Repl (Maybe Type)
iinfer g r t = case iType0 g r t of
  Left  e -> liftIO (T.putStrLn . renderErr $ prettyAnsi e) >> return Nothing
  Right v -> return (Just v)

iType0 :: Context -> ZeroOneMany -> ITerm -> Result Type
iType0 g r t = do
  (qs, tp) <- first (Map.map (r S.*)) <$> runReaderT (iType 0 (restrict r) t) g
  mapM_ (throwError . MultiplicityError Nothing) $ checkMultiplicity qs (snd g)
  return tp
 where
  restrict :: ZeroOneMany -> ZeroOne
  restrict Zero = Zero'
  restrict One  = One'
  restrict Many = One'

evalInEnv :: CTerm -> Judgement Value
evalInEnv t = asks (cEval t . (, []) . fst)

iType :: Int -> ZeroOne -> ITerm -> Judgement (Usage, Type)
-- Cut:
iType ii r (Ann e tyt) = do
  _  <- local (second forget) $ cType ii Zero' tyt VUniverse
  ty <- evalInEnv tyt
  qs <- cType ii r e ty
  return (qs, ty)
-- Var:
iType _ r (Free x) = do
  env <- asks snd
  case find ((== x) . bndName) env of
    Just (Binding _ _ ty) -> return (Map.singleton x $ extend r, ty)
    Nothing               -> throwError $ UnknownVar x
-- App:
iType ii r (e1 :$: e2) = do
  (qs1, si) <- iType ii r e1
  case si of
    VPi p ty ty' -> do
      let r' = extend r
      qs <- if p S.* r' == Zero
        then do
          _ <- cType ii Zero' e2 ty
          return qs1
        else do
          qs2 <- cType ii One' e2 ty
          return $ Map.unionWith (S.+) qs1 (Map.map (p S.* r' S.*) qs2)
      (qs, ) . ty' <$> evalInEnv e2
    ty -> throwError $ WrongInference "_ -> _" ty (e1 :$: e2)
-- PairElim:
iType ii r (PairElim l i t) = do
  (qs1, lTy) <- iType ii r l
  case lTy of
    zTy@(VTensor p xTy yTy) -> do
      qs3 <- cTypeAnn (Binding (Local ii) Zero zTy)
      let r' = extend r
      let x  = Binding (Local ii) (p S.* r') xTy
      let y = Binding (Local $ ii + 1) r' (yTy . vfree $ Local ii)
      local (second ([x, y] ++)) $ do
        txy <- evalInEnv (cSubst 0 (Ann (Pair (ifn x) (ifn y)) (quote0 zTy)) t)
        qs2 <- cTypeIn
          (cSubst 1 (Free $ bndName x) . cSubst 0 (Free $ bndName y) $ i)
          txy
        qs <-
          pure (Map.unionsWith (S.+) [qs1, qs2, qs3])
          >>= checkVar "pairElim, Local ii"   (bndName x)
          >>= checkVar "pairElim, Local ii+1" (bndName y)
        (qs, ) <$> evalInEnv (cSubst 0 l t)
    ty -> throwError
      $ WrongInference ("_" <+> multAnn "*" <+> "_") ty (PairElim l i t)
 where
  ifn = Inf . Free . bndName
  cTypeAnn z = local (second (forget . (z :)))
    $ cType (ii + 1) Zero' (cSubst 0 (Free $ bndName z) t) VUniverse
  cTypeIn ixy txy = cType (ii + 2) r ixy txy
-- UnitElim:
iType ii r (MUnitElim l i t) = do
  (qs1, lTy) <- iType ii r l
  case lTy of
    xTy@VMUnitType -> do
      qs3 <- cTypeAnn (Binding (Local ii) Zero xTy)
      tu  <- evalInEnv (cSubst 0 (Ann MUnit MUnitType) t)
      qs2 <- cTypeIn tu
      let qs = Map.unionsWith (S.+) [qs1, qs2, qs3]
      (qs, ) <$> evalInEnv (cSubst 0 l t)
    ty ->
      throwError $ WrongInference (prettyAnsi MUnitType) ty (MUnitElim l i t)
 where
  cTypeAnn x = local (second (forget . (x :)))
    $ cType (ii + 1) Zero' (cSubst 0 (Free $ bndName x) t) VUniverse
  cTypeIn tu = cType ii r i tu
-- Fst:
iType ii r (Fst i) = do
  (qs, ty) <- iType ii r i
  case ty of
    (VWith s _) -> return (qs, s)
    _ -> throwError $ WrongInference ("_" <+> addAnn "&" <+> "_") ty (Fst i)
-- Snd:
iType ii r (Snd i) = do
  (qs, ty) <- iType ii r i
  case ty of
    (VWith _ t) -> return (qs, t . vfree $ Local ii)
    _ -> throwError $ WrongInference ("_" <+> addAnn "&" <+> "_") ty (Snd i)
iType _ _ i@(Bound _) = error $ "internal: Trying to infer type of " <> show i

cType :: Int -> ZeroOne -> CTerm -> Type -> Judgement Usage
-- Elim
cType ii r (Inf e) v = do
  (qs, v') <- iType ii r e
  unless (quote0 v == quote0 v')
         (throwError $ WrongInference (prettyAnsi v) v' e)
  return qs
-- Lam:
cType ii r (Lam e) (VPi p ty ty') = do
  let x = Binding (Local ii) (p S.* extend r) ty
  local (second (x :)) $ do
    qs <- cType (ii + 1)
                r
                (cSubst 0 (Free $ bndName x) e)
                (ty' . vfree $ bndName x)
    checkVar "lam" (bndName x) qs
-- Universe:
cType _  _ Universe          VUniverse = return Map.empty
-- Fun:
cType ii r t@(Pi _ tyt tyt') VUniverse = do
  unless (r == Zero') (throwError . ErasureError t $ extend r)
  _ <- local (second forget) $ cType ii r tyt VUniverse
  x <- Binding (Local ii) Zero <$> evalInEnv tyt
  local (second (forget . (x :)))
    $   cType (ii + 1) r (cSubst 0 (Free $ bndName x) tyt') VUniverse
    >>= checkVar "fun" (bndName x)
-- Pair:
cType ii r (Pair e1 e2) (VTensor p ty ty') = do
  let r' = extend r
  if p S.* r' == Zero
    then do
      _ <- cType ii Zero' e1 ty
      rest
    else do
      qs1 <- cType ii One' e1 ty
      qs2 <- rest
      return $ Map.unionWith (S.+) qs2 (Map.map (p S.* r' S.*) qs1)
  where rest = evalInEnv e1 >>= (cType ii r e2 . ty')
-- Tensor:
cType ii r t@(Tensor _ tyt tyt') VUniverse = do
  unless (r == Zero') (throwError . ErasureError t $ extend r)
  _ <- local (second forget) $ cType ii r tyt VUniverse
  x <- Binding (Local ii) Zero <$> evalInEnv tyt
  local (second (forget . (x :)))
    $   cType (ii + 1) r (cSubst 0 (Free $ bndName x) tyt') VUniverse
    >>= checkVar "tensor" (bndName x)
-- Unit:
cType _  _ MUnit          VMUnitType     = return Map.empty
-- UnitType:
cType _  _ MUnitType      VUniverse      = return Map.empty
-- Angles:
cType ii r (Angles e1 e2) (VWith ty ty') = do
  qs1 <- cType ii r e1 ty
  qs2 <- evalInEnv e1 >>= (cType ii r e2 . ty')
  return $ Map.unionWith combine qs1 qs2
 where
  combine Zero Zero = Zero
  combine One  One  = One
  combine _    _    = Many
-- With:
cType ii r t@(With tyt tyt') VUniverse = do
  unless (r == Zero') (throwError . ErasureError t $ extend r)
  _ <- local (second forget) $ cType ii r tyt VUniverse
  x <- Binding (Local ii) Zero <$> evalInEnv tyt
  local (second (forget . (x :)))
    $   cType (ii + 1) r (cSubst 0 (Free $ bndName x) tyt') VUniverse
    >>= checkVar "with" (bndName x)
-- AUnit:
cType _ _ AUnit     VAUnitType = return Map.empty
-- AUnitType:
cType _ _ AUnitType VUniverse  = return Map.empty
cType _ _ val       ty         = throwError $ WrongCheck ty val

checkVar :: String -> Name -> Usage -> Judgement Usage
checkVar loc n qs = do
  env <- asks snd
  let (q, qs') = splitVar n qs
  mapM_ (throwError . MultiplicityError (Just loc))
        (checkMultiplicity (Map.singleton n q) env)
  return qs'
 where
  splitVar :: Name -> Usage -> (ZeroOneMany, Usage)
  splitVar = (first (fromMaybe Zero) .) . Map.alterF (, Nothing)

checkMultiplicity
  :: Usage -> TypeEnv -> Maybe [(Name, Type, ZeroOneMany, ZeroOneMany)]
checkMultiplicity qs env = Map.foldrWithKey
  (\n q es -> case find ((== n) . bndName) env of
    Just b | q <: bndUsage b -> es
           | otherwise -> Just $ (n, bndType b, q, bndUsage b) : fromMaybe [] es
    Nothing ->
      error ("internal: Unknown " <> show n <> " used " <> show q <> "-times")
  )
  Nothing
  qs

