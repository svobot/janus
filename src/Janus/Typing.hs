-- | Implementation of the typing algorithm.
--
-- This module exports the @synthesise@ function, which synthesises the type of
-- a given term, according to the typing rules described in our paper.
module Janus.Typing
  ( ExpectedType(..)
  , Result
  , TypeError(..)
  , synthesise
  ) where

import           Control.Monad.Except           ( throwError )
import           Control.Monad.Reader           ( MonadReader(local)
                                                , ReaderT(runReaderT)
                                                , asks
                                                , unless
                                                )
import           Data.Bifunctor                 ( first )
import           Data.Function                  ( on )
import           Data.List                      ( find )
import qualified Data.Map.Merge.Strict         as Map
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( fromMaybe
                                                , mapMaybe
                                                )
import           Janus.Semiring
import           Janus.Types

-- | Record of bound variables.
data TypingConfig = TypingConfig
  { -- | Variables which have been bound in some previous term.
    cfgGlobalContext :: Context
  , -- | Variables which have a binding occurrence in the currently judged term.
    cfgBoundLocals   :: TypeEnv
  }

-- | Add new variable binding to the local environment.
with :: Binding Name ZeroOneMany Type -> TypingConfig -> TypingConfig
with b cfg = cfg { cfgBoundLocals = b : cfgBoundLocals cfg }

-- | Get the type bindings of the local and global variables.
typeEnv :: TypingConfig -> TypeEnv
typeEnv (TypingConfig (_, globals) locals) = locals ++ globals

-- | A monad transformer which carries the context for the typing algorithm.
type Judgment = ReaderT TypingConfig Result

-- | Record of how much of each variable is consumed in a term.
type Usage = Map.Map Name ZeroOneMany

-- | Evaluate the term in context provided by the judgment.
evalInEnv :: CTerm -> Judgment Value
evalInEnv m = asks (flip cEval m . (, []) . fst . cfgGlobalContext)

-- | Create a local variable with a fresh name.
newLocalVar :: a -> b -> Judgment (Binding Name a b)
newLocalVar s ty = do
  i <- asks $ length . cfgBoundLocals
  return $ Binding (Local i) s ty

-- | Extend the typing context with a local variable.
withLocalVar
  :: String -> Binding Name ZeroOneMany Type -> Judgment Usage -> Judgment Usage
withLocalVar loc v jud = local (with v) $ jud >>= checkVar (bndName v)
 where
  -- If usage of a local variable doesn't match available resources,
  -- judgment fails.
  checkVar :: Name -> Usage -> Judgment Usage
  checkVar n qs = do
    env <- asks typeEnv
    let (q, qs') = splitVar n qs
    mapM_ (throwError . UsageError (Just loc))
          (checkUsage env $ Map.singleton n q)
    return qs'

  splitVar = (first (fromMaybe zero) .) . Map.alterF (, Nothing)

-- | Check that the usage fits the resources available in the environment.
checkUsage
  :: TypeEnv -> Usage -> Maybe [(Name, Type, ZeroOneMany, ZeroOneMany)]
checkUsage env = toMaybe . mapMaybe notEnough . Map.toList
 where
  notEnough (n, q) = case find ((== n) . bndName) env of
    Just b | q `fitsIn` bndUsage b -> Nothing
           | otherwise             -> Just (n, bndType b, q, bndUsage b)
    Nothing ->
      error $ "internal: Unknown " <> show n <> " used " <> show q <> "-times"
  toMaybe [] = Nothing
  toMaybe es = Just es

-- | Expected type of a term during a type clash error.
data ExpectedType = FnAppExp | MPairExp | APairExp | TypeExp Type

-- | Errors that can arise during the typing algorithm.
data TypeError
   = -- | Usage of a variable in the term is incompatible with the available
     -- quantity of that variable in the context. We can report list of multiple
     -- incompatible variables at once.
     UsageError (Maybe String) [(Name, Type, ZeroOneMany, ZeroOneMany)]
   | -- | Type has a computational presence.
     ErasureError CTerm ZeroOneMany
   | -- | Type synthesised from the term doesn't match type the rule expects.
     TypeClashError ExpectedType Type ITerm
   | -- | No typing rule was applicable for the given combination of term and
     -- type.
     CheckError Type CTerm
   | -- | Term uses a variable that is missing in the context.
     UnknownVarError Name

type Result = Either TypeError

-- | Synthesise the type of a term and check that context has appropriate
-- resources available for the term.
synthesise :: Context -> ZeroOneMany -> ITerm -> Result Type
synthesise ctx s m = do
  (qs, tp) <- first (Map.map (s .*.))
    <$> runReaderT (synthType (relevance s) m) (TypingConfig ctx [])
  mapM_ (throwError . UsageError Nothing) $ checkUsage (snd ctx) qs
  return tp

-- | Synthesise the type of a term.
synthType :: Relevance -> ITerm -> Judgment (Usage, Type)
synthType s (Ann m t) = do
  checkTypeErased t VUniverse
  ty <- evalInEnv t
  qs <- checkType s m ty
  return (qs, ty)
synthType s (Free x) = do
  env <- asks typeEnv
  case find ((== x) . bndName) env of
    Just (Binding _ _ ty) -> return (Map.singleton x $ extend s, ty)
    Nothing               -> throwError $ UnknownVarError x
synthType s (m :$: n) = do
  (qs1, si) <- synthType s m
  case si of
    VPi p ty ty' -> do
      qs <- case extend s .*. p of
        Zero -> checkTypeErased n ty >> return qs1
        sp ->
          Map.unionWith (.+.) qs1 . Map.map (sp .*.) <$> checkType Present n ty
      (qs, ) . ty' <$> evalInEnv n
    ty -> throwError $ TypeClashError FnAppExp ty (m :$: n)
synthType s (MPairElim m n o) = do
  (qs1, mTy) <- synthType s m
  case mTy of
    zTy@(VMPairType p xTy yTy) -> do
      z <- newLocalVar zero zTy
      local (with z) $ checkTypeErased (sub 0 z o) VUniverse
      let s' = extend s
      x  <- newLocalVar (p .*. s') xTy
      qs <- withLocalVar "First element of the pair elimination" x $ do
        y <- newLocalVar s' (yTy . vfree $ bndName x)
        withLocalVar "Second element of the pair elimination" y $ do
          oxy <- evalInEnv
            $ cSubst 0 (Ann (MPair (ifn x) (ifn y)) $ quote0 zTy) o
          qs2 <- checkType s (sub 1 x . sub 0 y $ n) oxy
          return $ Map.unionWith (.+.) qs1 qs2
      (qs, ) <$> evalInEnv (cSubst 0 m o)
    ty -> throwError $ TypeClashError MPairExp ty (MPairElim m n o)
 where
  ifn = Inf . Free . bndName
  sub i = cSubst i . Free . bndName
synthType s (MUnitElim m n o) = do
  (qs1, mTy) <- synthType s m
  case mTy of
    xTy@VMUnitType -> do
      x <- newLocalVar zero xTy
      local (with x) $ checkTypeErased (cSubst 0 (Free $ bndName x) o) VUniverse
      ox  <- evalInEnv (cSubst 0 (Ann MUnit MUnitType) o)
      qs2 <- checkType s n ox
      (Map.unionWith (.+.) qs1 qs2, ) <$> evalInEnv (cSubst 0 m o)
    ty -> throwError $ TypeClashError (TypeExp VMUnitType) ty (MUnitElim m n o)
synthType s (Fst m) = do
  (qs, ty) <- synthType s m
  case ty of
    VAPairType t1 _ -> return (qs, t1)
    _               -> throwError $ TypeClashError APairExp ty (Fst m)
synthType s (Snd m) = do
  (qs, ty) <- synthType s m
  case ty of
    VAPairType _ t2 -> (qs, ) . t2 <$> evalInEnv (Inf $ Fst m)
    _               -> throwError $ TypeClashError APairExp ty (Snd m)
synthType _ i@(Bound _) =
  error $ "internal: Trying to infer type of " <> show i

-- | Type-check a term.
checkType :: Relevance -> CTerm -> Type -> Judgment Usage
checkType s (Inf m) ty = do
  (qs, ty') <- synthType s m
  unless (((==) `on` quote0) ty ty')
         (throwError $ TypeClashError (TypeExp ty) ty' m)
  return qs
checkType s (Lam m) (VPi p ty ty') = do
  x <- newLocalVar (p .*. extend s) ty
  withLocalVar "Lambda abstraction" x
    $ checkType s (cSubst 0 (Free $ bndName x) m) (ty' . vfree $ bndName x)
checkType s (MPair m n) (VMPairType p t1 t2) = do
  case extend s .*. p of
    Zero -> checkTypeErased m t1 >> rest
    sp ->
      Map.unionWith (.+.)
        <$> (Map.map (sp .*.) <$> checkType Present m t1)
        <*> rest
  where rest = evalInEnv m >>= (checkType s n . t2)
checkType s (APair m n) (VAPairType t1 t2) = do
  qs1 <- checkType s m t1
  qs2 <- evalInEnv m >>= (checkType s n . t2)
  -- For every resource that is used anywhere in the pair, take the least upper
  -- bound of the resource usages in both elements of the pair. The element that
  -- is missing a usage of a resource is considered to use it zero-times.
  return $ Map.merge (Map.mapMissing (const $ lub zero))
                     (Map.mapMissing (const $ lub zero))
                     (Map.zipWithMatched (const lub))
                     qs1
                     qs2
checkType _ MUnit                  VMUnitType = return Map.empty
checkType _ AUnit                  VAUnitType = return Map.empty
checkType s ty@(Pi        _ t1 t2) VUniverse  = checkTypeDep s ty t1 t2
checkType s ty@(MPairType _ t1 t2) VUniverse  = checkTypeDep s ty t1 t2
checkType s ty@(APairType t1 t2  ) VUniverse  = checkTypeDep s ty t1 t2
checkType s ty@Universe            VUniverse  = checkTypeAtom s ty
checkType s ty@MUnitType           VUniverse  = checkTypeAtom s ty
checkType s ty@AUnitType           VUniverse  = checkTypeAtom s ty
checkType _ m                      ty         = throwError $ CheckError ty m

-- | Type-check a dependent type.
checkTypeDep :: Relevance -> CTerm -> CTerm -> CTerm -> Judgment Usage
checkTypeDep s ty t1 t2 = case s of
  Erased -> do
    checkTypeErased t1 VUniverse
    x <- evalInEnv t1 >>= newLocalVar zero
    local (with x) $ checkTypeErased (cSubst 0 (Free $ bndName x) t2) VUniverse
    return Map.empty
  -- Types cannot consume any resources, so the judgment fails if the typing
  -- is not done in the erased context.
  Present -> throwError . ErasureError ty $ extend s

-- | Type-check an atomic type.
checkTypeAtom :: Relevance -> CTerm -> Judgment Usage
checkTypeAtom s ty = case s of
  Erased  -> return Map.empty
  -- Types cannot consume any resources, so the judgment fails if the typing
  -- is not done in the erased context.
  Present -> throwError . ErasureError ty $ extend s

-- | Type-check a term in erased context.
checkTypeErased :: CTerm -> Type -> Judgment ()
checkTypeErased m ty = do
  errs <- Map.filter (/= zero) <$> checkType Erased m ty
  -- Having a non-zero usage of a variable in the erased context means that
  -- there is something wrong with the type checking algorithm; throw an error.
  unless (Map.null errs) $ error
    ( unlines
    $ "internal: Variables used in the erased context:"
    : [ "    " <> show k <> " used " <> show q <> "-times"
      | (k, q) <- Map.toList errs
      ]
    )

