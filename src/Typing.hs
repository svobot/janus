{-# LANGUAGE TupleSections #-}

module Typing where

import           Control.Monad                  ( unless )
import           Control.Monad.Except           ( throwError
                                                , when
                                                )
import           Control.Monad.Trans            ( liftIO )
import           Data.Bifunctor                 ( first
                                                , second
                                                )
import           Data.List                      ( find )
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( fromMaybe )
import qualified Data.Semiring                 as S
import           Data.Text.Prettyprint.Doc
import           Printer
import           Rig
import           Types

import           Debug.Trace                    ( traceM )

type Usage = Map.Map Name ZeroOneMany

iinfer :: (NameEnv, Context) -> ZeroOneMany -> ITerm -> Repl (Maybe Type)
iinfer g r t = case iType0 g r t of
  Left  e -> liftIO $ putStrLn e >> return Nothing
  Right v -> return (Just v)

iType0 :: (NameEnv, Context) -> ZeroOneMany -> ITerm -> Result Type
iType0 g r t = do
  (qs, tp) <- first (Map.map (r S.*)) <$> iType 0 g (restrict r) t
  mapM_ (throwError . render . ("Unavailable resources:" <>) . nest 2)
    $ errs qs (snd g)
  return tp
 where
  restrict :: ZeroOneMany -> ZeroOne
  restrict Zero = Zero'
  restrict One  = One'
  restrict Many = One'

iType :: Int -> (NameEnv, Context) -> ZeroOne -> ITerm -> Result (Usage, Type)
-- Cut:
iType ii g r (Ann e tyt) = do
  _ <- cType ii (second forget g) Zero' tyt VStar
  let ty = cEval tyt (fst g, [])
  qs <- cType ii g r e ty
  return (qs, ty)
-- Var:
iType _ g r (Free x) = case find ((== x) . bndName) (snd g) of
  Just (Binding _ q ty) -> do
    when (q /= extend r) $ traceM
      (  "VAR "
      ++ show x
      ++ " : "
      ++ show ty
      ++ "\n  context: "
      ++ show q
      ++ "\n     used: "
      ++ show (extend r :: ZeroOneMany)
      )
    return (Map.singleton x $ extend r, ty)
  Nothing -> throwError ("unknown identifier: " ++ render (pretty $ Free x))
-- App:
iType ii g r (e1 :@: e2) = do
  (qs1, si) <- iType ii g r e1
  case si of
    VPi p ty ty' -> do
      let r' = extend r
      qs <- if p S.* r' == Zero
        then do
          _ <- cType ii g Zero' e2 ty
          return qs1
        else do
          qs2 <- cType ii g One' e2 ty
          return $ Map.unionWith (S.+) qs1 (Map.map (p S.* r' S.*) qs2)
      return (qs, ty' $ cEval e2 (fst g, []))
    _ -> throwError "illegal application"
-- PairElim:
iType ii g r (PairElim l i t) = do
  (qs1, lTy) <- iType ii g r l
  case lTy of
    zTy@(VTensor p xTy yTy) -> do
      qs3 <- cTypeAnn (Binding (Local ii) Zero zTy)
      let r'  = extend r
      let x   = Binding (Local ii) (p S.* r') xTy
      let y = Binding (Local $ ii + 1) r' (yTy . vfree $ Local ii)
      let gxy = second ([x, y] ++) g
      let
        txy = cEval
          (cSubst
            0
            (Ann (Pair (Inf . Free $ bndName x) (Inf . Free $ bndName y))
                 (quote0 zTy)
            )
            t
          )
          (fst gxy, [])
      qs2 <- cTypeIn
        gxy
        (cSubst 1 (Free $ bndName x) . cSubst 0 (Free $ bndName y) $ i)
        txy
      qs <-
        pure (Map.unionsWith (S.+) [qs1, qs2, qs3])
        >>= checkVar "pairElim, Local ii"   (bndName x) (snd gxy)
        >>= checkVar "pairElim, Local ii+1" (bndName y) (snd gxy)
      let tl = cEval (cSubst 0 l t) (fst gxy, [])
      return (qs, tl)
    _ -> throwError "illegal pair elimination"
 where
  cTypeAnn z = cType (ii + 1)
                     (second (forget . (z :)) g)
                     Zero'
                     (cSubst 0 (Free $ bndName z) t)
                     VStar
  cTypeIn gxy ixy txy = cType (ii + 2) gxy r ixy txy
-- UnitElim:
iType ii g r (MUnitElim l i t) = do
  (qs1, lTy) <- iType ii g r l
  case lTy of
    xTy@VMUnitType -> do
      qs3 <- cTypeAnn (Binding (Local ii) Zero xTy)
      let tu = cEval (cSubst 0 (Ann MUnit MUnitType) t) (fst g, [])
      qs2 <- cTypeIn tu
      let qs = Map.unionsWith (S.+) [qs1, qs2, qs3]
      let tl = cEval (cSubst 0 l t) (fst g, [])
      return (qs, tl)
    _ -> throwError "illegal unit elimination"
 where
  cTypeAnn x = cType (ii + 1)
                     (second (forget . (x :)) g)
                     Zero'
                     (cSubst 0 (Free $ bndName x) t)
                     VStar
  cTypeIn tu = cType ii g r i tu
-- Fst:
iType ii g r (Fst i) = do
  (qs, ty) <- iType ii g r i
  case ty of
    (VWith s _) -> return (qs, s)
    _           -> throwError "illegal fst elimination"
-- Snd:
iType ii g r (Snd i) = do
  (qs, ty) <- iType ii g r i
  case ty of
    (VWith _ t) -> return (qs, t . vfree $ Local ii)
    _           -> throwError "illegal fst elimination"
iType _ _ _ _ = throwError "type mismatch (iType)"

cType :: Int -> (NameEnv, Context) -> ZeroOne -> CTerm -> Type -> Result Usage
-- Elim
cType ii g r (Inf e) v = do
  (qs, v') <- iType ii g r e
  unless
    (quote0 v == quote0 v')
    (  throwError
    $  "type mismatch:\n"
    ++ "type inferred:  "
    ++ render (pretty $ quote0 v')
    ++ "\n"
    ++ "type expected:  "
    ++ render (pretty $ quote0 v)
    ++ "\n"
    ++ "for expression: "
    ++ render (pretty e)
    )
  return qs
-- Lam:
cType ii g r (Lam e) (VPi p ty ty') = do
  let x       = Binding (Local ii) (p S.* extend r) ty
  let local_g = second (x :) g
  qs <- cType (ii + 1)
              local_g
              r
              (cSubst 0 (Free $ bndName x) e)
              (ty' . vfree $ bndName x)
  checkVar "lam" (bndName x) (snd local_g) qs
-- Star:
cType _  _ _       Star            VStar = return Map.empty
-- Fun:
cType ii g r@Zero' (Pi _ tyt tyt') VStar = do
  _ <- cType ii (second forget g) r tyt VStar
  let x       = Binding (Local ii) Zero $ cEval tyt (fst g, [])
  let local_g = second (forget . (x :)) g
  qs <- cType (ii + 1) local_g r (cSubst 0 (Free $ bndName x) tyt') VStar
  checkVar "fun" (bndName x) (snd local_g) qs
-- Pair:
cType ii g r (Pair e1 e2) (VTensor p ty ty') = do
  let r' = extend r
  if p S.* r' == Zero
    then do
      _ <- cType ii g Zero' e1 ty
      rest
    else do
      qs1 <- cType ii g One' e1 ty
      qs2 <- rest
      return $ Map.unionWith (S.+) qs2 (Map.map (p S.* r' S.*) qs1)
 where
  rest = do
    let e1v = cEval e1 (fst g, [])
    cType ii g r e2 (ty' e1v)
-- Tensor:
cType ii g r@Zero' (Tensor _ tyt tyt') VStar = do
  _ <- cType ii (second forget g) r tyt VStar
  let x       = Binding (Local ii) Zero $ cEval tyt (fst g, [])
  let local_g = second (forget . (x :)) g
  qs <- cType (ii + 1) local_g r (cSubst 0 (Free $ bndName x) tyt') VStar
  checkVar "tensor" (bndName x) (snd local_g) qs
-- Unit:
cType _  _ _ MUnit          VMUnitType     = return Map.empty
-- UnitType:
cType _  _ _ MUnitType      VStar          = return Map.empty
-- Angles:
cType ii g r (Angles e1 e2) (VWith ty ty') = do
  qs1 <- cType ii g r e1 ty
  let e1v = cEval e1 (fst g, [])
  qs2 <- cType ii g r e2 (ty' e1v)
  return $ Map.unionWith combine qs1 qs2
 where
  combine Zero Zero = Zero
  combine One  One  = One
  combine _    _    = Many
-- With:
cType ii g r@Zero' (With tyt tyt') VStar = do
  _ <- cType ii (second forget g) r tyt VStar
  let x       = Binding (Local ii) Zero $ cEval tyt (fst g, [])
  let local_g = second (forget . (x :)) g
  qs <- cType (ii + 1) local_g r (cSubst 0 (Free $ bndName x) tyt') VStar
  checkVar "with" (bndName x) (snd local_g) qs
-- AUnit:
cType _ _ _ AUnit     VAUnitType = return Map.empty
-- AUnitType:
cType _ _ _ AUnitType VStar      = return Map.empty
cType _ _ _ _         _          = throwError "type mismatch (cType)"

checkVar :: String -> Name -> Context -> Usage -> Result Usage
checkVar loc n ctx qs = do
  let (q, qs') = splitVar n qs
  mapM_
    ( throwError
    . render
    . (("Unavailable resources (" <> pretty loc <> "):") <>)
    . nest 2
    )
    (errs (Map.singleton n q) ctx)
  return qs'
 where
  splitVar :: Name -> Usage -> (ZeroOneMany, Usage)
  splitVar = (first (fromMaybe Zero) .) . Map.alterF (, Nothing)

errs :: Usage -> Context -> Maybe (Doc ann)
errs qs ctx = Map.foldlWithKey'
  (\es n q -> case find ((== n) . bndName) ctx of
    Just b
      | q <: bndUsage b -> es
      | otherwise -> Just $ fromMaybe emptyDoc es <> hardline <> nest
        2
        (vsep
          [ pretty n <+> ":" <+> pretty (bndType b)
          , "Used"
          <+> pretty q
          <>  "-times, but only available"
          <+> pretty (bndUsage b)
          <>  "-times."
          ]
        )
    Nothing -> error
      ("internal: Unavailable " <> show n <> " used " <> show q <> "-times")
  )
  Nothing
  qs

