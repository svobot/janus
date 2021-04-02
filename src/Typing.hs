module Typing
  ( iinfer
  , iType0
  ) where

import           Control.Monad.Except           ( throwError )
import           Control.Monad.Reader           ( MonadIO(liftIO)
                                                , MonadReader(local)
                                                , ReaderT(runReaderT)
                                                , asks
                                                , unless
                                                )
import           Data.Bifunctor                 ( first )
import           Data.List                      ( find )
import qualified Data.Map.Merge.Strict         as Map
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( fromMaybe
                                                , mapMaybe
                                                )
import qualified Data.Semiring                 as S
import qualified Data.Text.IO                  as T
import           Printer
import           Rig
import           Types

type Usage = Map.Map Name ZeroOneMany
data TypingConfig = TypingConfig
  { cfgGlobalContext :: Context
  , cfgBoundLocals   :: TypeEnv
  }
type Judgement = ReaderT TypingConfig Result

iinfer :: Context -> ZeroOneMany -> ITerm -> Repl (Maybe Type)
iinfer g r t = case iType0 g r t of
  Left  e -> liftIO (T.putStrLn . render $ pretty e) >> return Nothing
  Right v -> return (Just v)

iType0 :: Context -> ZeroOneMany -> ITerm -> Result Type
iType0 g r t = do
  (qs, tp) <- first (Map.map (r S.*))
    <$> runReaderT (iType (restrict r) t) (TypingConfig g [])
  mapM_ (throwError . MultiplicityError Nothing) $ checkMultiplicity (snd g) qs
  return tp
 where
  restrict :: ZeroOneMany -> ZeroOne
  restrict Zero = Zero'
  restrict One  = One'
  restrict Many = One'

erased :: TypingConfig -> TypingConfig
erased (TypingConfig (vs, ts) bs) = TypingConfig (vs, forget ts) (forget bs)

with :: Binding Name ZeroOneMany Type -> TypingConfig -> TypingConfig
with b cfg = cfg { cfgBoundLocals = b : cfgBoundLocals cfg }

bind :: ZeroOneMany -> Type -> TypingConfig -> Binding Name ZeroOneMany Type
bind r ty (TypingConfig _ bs) = Binding (Local (length bs)) r ty

typeEnv :: TypingConfig -> TypeEnv
typeEnv (TypingConfig (_, ts) bs) = bs ++ ts

evalInEnv :: CTerm -> Judgement Value
evalInEnv t = asks (cEval t . (, []) . fst . cfgGlobalContext)

-- | Infer the type and count the resource usage of the term.
iType :: ZeroOne -> ITerm -> Judgement (Usage, Type)
iType r (Ann e tyt) = do
  local erased (cType Zero' tyt VUniverse) >>= checkErased
  ty <- evalInEnv tyt
  qs <- cType r e ty
  return (qs, ty)
iType r (Free x) = do
  env <- asks typeEnv
  case find ((== x) . bndName) env of
    Just (Binding _ _ ty) -> return (Map.singleton x $ extend r, ty)
    Nothing               -> throwError $ UnknownVarError x
iType r (e1 :$: e2) = do
  (qs1, si) <- iType r e1
  case si of
    VPi p ty ty' -> do
      let r' = extend r
      qs <- if p S.* r' == Zero
        then do
          _ <- cType Zero' e2 ty
          return qs1
        else do
          qs2 <- cType One' e2 ty
          return $ Map.unionWith (S.+) qs1 (Map.map (p S.* r' S.*) qs2)
      (qs, ) . ty' <$> evalInEnv e2
    ty -> throwError $ InferenceError "_ -> _" ty (e1 :$: e2)
iType r (PairElim l i t) = do
  (qs1, lTy) <- iType r l
  case lTy of
    zTy@(VTensor p xTy yTy) -> do
      z <- asks $ bind Zero zTy
      local (erased . with z)
            (cType Zero' (cSubst 0 (Free $ bndName z) t) VUniverse)
        >>= checkErased
      let r' = extend r
      x <- asks $ bind (p S.* r') xTy
      local (with x) $ do
        y <- asks $ bind r' (yTy . vfree $ bndName x)
        local (with y) $ do
          txy <- evalInEnv
            (cSubst 0 (Ann (Pair (ifn x) (ifn y)) (quote0 zTy)) t)
          qs2 <- cType
            r
            (cSubst 1 (Free $ bndName x) . cSubst 0 (Free $ bndName y) $ i)
            txy
          qs <-
            pure (Map.unionWith (S.+) qs1 qs2)
            >>= checkVar "First element of the pair elimination"  (bndName x)
            >>= checkVar "Second element of the pair elimination" (bndName y)
          (qs, ) <$> evalInEnv (cSubst 0 l t)
    ty -> throwError
      $ InferenceError ("_" <+> mult "*" <+> "_") ty (PairElim l i t)
  where ifn = Inf . Free . bndName
iType r (MUnitElim l i t) = do
  (qs1, lTy) <- iType r l
  case lTy of
    xTy@VMUnitType -> do
      x <- asks $ bind Zero xTy
      local (erased . with x)
            (cType Zero' (cSubst 0 (Free $ bndName x) t) VUniverse)
        >>= checkErased
      tu  <- evalInEnv (cSubst 0 (Ann MUnit MUnitType) t)
      qs2 <- cType r i tu
      let qs = Map.unionWith (S.+) qs1 qs2
      (qs, ) <$> evalInEnv (cSubst 0 l t)
    ty -> throwError $ InferenceError (pretty MUnitType) ty (MUnitElim l i t)
iType r (Fst i) = do
  (qs, ty) <- iType r i
  case ty of
    (VWith s _) -> return (qs, s)
    _ -> throwError $ InferenceError ("_" <+> add "&" <+> "_") ty (Fst i)
iType r (Snd i) = do
  (qs, ty) <- iType r i
  case ty of
    (VWith _ t) -> (qs, ) . t <$> evalInEnv (Inf $ Fst i)
    _ -> throwError $ InferenceError ("_" <+> add "&" <+> "_") ty (Snd i)
iType _ i@(Bound _) = error $ "internal: Trying to infer type of " <> show i

-- | Check the type and count the resource usage of the term.
cType :: ZeroOne -> CTerm -> Type -> Judgement Usage
cType r (Inf e) v = do
  (qs, v') <- iType r e
  unless (quote0 v == quote0 v') (throwError $ InferenceError (pretty v) v' e)
  return qs
cType r (Lam e) (VPi p ty ty') = do
  x <- asks $ bind (p S.* extend r) ty
  local (with x)
    $   cType r (cSubst 0 (Free $ bndName x) e) (ty' . vfree $ bndName x)
    >>= checkVar "Lambda abstraction" (bndName x)
cType r (Pair e1 e2) (VTensor p ty ty') = do
  let r' = extend r
  if p S.* r' == Zero
    then do
      _ <- cType Zero' e1 ty
      rest
    else do
      qs1 <- cType One' e1 ty
      qs2 <- rest
      return $ Map.unionWith (S.+) qs2 (Map.map (p S.* r' S.*) qs1)
  where rest = evalInEnv e1 >>= (cType r e2 . ty')
cType r (Angles e1 e2) (VWith ty ty') = do
  qs1 <- cType r e1 ty
  qs2 <- evalInEnv e1 >>= (cType r e2 . ty')
  -- For every resource that is used anywhere in the pair, take the least upper
  -- bound of the resource usages in both elements of the pair. The element that
  -- is missing a usage of a resource is considered to use it zero-times.
  return $ Map.merge (Map.mapMissing (const $ lub Zero))
                     (Map.mapMissing (const $ lub Zero))
                     (Map.zipWithMatched (const lub))
                     qs1
                     qs2
 where
  lub Zero Zero = Zero
  lub One  One  = One
  lub _    _    = Many
cType r t@(Pi     _ t1 t2) VUniverse  = cTypeDependent "Pi type" r t t1 t2
cType r t@(Tensor _ t1 t2) VUniverse  = cTypeDependent "Tensor type" r t t1 t2
cType r t@(With t1 t2    ) VUniverse  = cTypeDependent "With type" r t t1 t2
cType _ Universe           VUniverse  = return Map.empty
cType _ MUnit              VMUnitType = return Map.empty
cType _ MUnitType          VUniverse  = return Map.empty
cType _ AUnit              VAUnitType = return Map.empty
cType _ AUnitType          VUniverse  = return Map.empty
cType _ val                ty         = throwError $ CheckError ty val

-- | Generic typing rule that check terms containing a dependent function type,
-- dependent tensor product type, or a dependent with type
cTypeDependent
  :: String -> ZeroOne -> CTerm -> CTerm -> CTerm -> Judgement Usage
cTypeDependent loc r t tyt tyt' = do
  unless (r == Zero') (throwError . ErasureError t $ extend r)
  local erased $ do
    cType r tyt VUniverse >>= checkErased
    x <- asks (flip $ bind Zero) <*> evalInEnv tyt
    local (with x)
      $   cType r (cSubst 0 (Free $ bndName x) tyt') VUniverse
      >>= checkVar loc (bndName x)

checkVar :: String -> Name -> Usage -> Judgement Usage
checkVar loc n qs = do
  env <- asks typeEnv
  let (q, qs') = splitVar n qs
  mapM_ (throwError . MultiplicityError (Just loc))
        (checkMultiplicity env $ Map.singleton n q)
  return qs'
 where
  splitVar :: Name -> Usage -> (ZeroOneMany, Usage)
  splitVar = (first (fromMaybe Zero) .) . Map.alterF (, Nothing)

checkMultiplicity
  :: TypeEnv -> Usage -> Maybe [(Name, Type, ZeroOneMany, ZeroOneMany)]
checkMultiplicity env = toMaybe . mapMaybe notEnough . Map.toList
 where
  notEnough (n, q) = case find ((== n) . bndName) env of
    Just b | q <: bndUsage b -> Nothing
           | otherwise       -> Just (n, bndType b, q, bndUsage b)
    Nothing ->
      error $ "internal: Unknown " <> show n <> " used " <> show q <> "-times"
  toMaybe [] = Nothing
  toMaybe es = Just es

-- | Checks that the usages returned from typing an expression in the erased
-- context are all Zero.
checkErased :: Usage -> Judgement ()
checkErased qs = do
  let bad = Map.filter (/= Zero) qs
  unless
    (Map.null bad)
    (  error
    $  "internal: Variables used in the erased context: \n"
    <> Map.foldrWithKey
         (\k v -> (<> "    " <> show k <> " used " <> show v <> "-times\n"))
         ""
         bad
    )
