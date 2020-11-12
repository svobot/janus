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
import           Printer
import           Text.PrettyPrint               ( render )
import           Types

import           Debug.Trace                    ( traceM )

data ZeroOne = Rig0' | Rig1' deriving (Eq)

extend :: ZeroOne -> ZeroOneMany
extend Rig0' = Zero
extend Rig1' = One

type Usage = Map.Map Name ZeroOneMany

iinfer :: (NameEnv, Context) -> ZeroOneMany -> ITerm -> Repl (Maybe Type)
iinfer g r t = case iType0 g r t of
  Left  e -> liftIO $ putStrLn e >> return Nothing
  Right v -> return (Just v)

iType0 :: (NameEnv, Context) -> ZeroOneMany -> ITerm -> Result Type
iType0 g r t = do
  let r' = restrict r
  (qs', tp) <- iType 0 g r' t
  let qs = Map.map (r S.*) qs'
  unless (qs `fits` snd g)
         (throwError $ "unavailable resources:\n" ++ err qs (snd g))
  return tp
 where
  restrict :: ZeroOneMany -> ZeroOne
  restrict Zero = Rig0'
  restrict One  = Rig1'
  restrict Many = Rig1'

  fits :: Usage -> Context -> Bool
  fits qs ctx =
    all
        (\(n, q) -> case find ((== n) . bndName) ctx of
          Just b  -> q <: bndUsage b
          Nothing -> False
        )
      $ Map.toList qs

iType :: Int -> (NameEnv, Context) -> ZeroOne -> ITerm -> Result (Usage, Type)
-- Cut:
iType ii g r (Ann e tyt) = do
  _ <- cType ii (second forget g) Rig0' tyt VStar
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
      ++ show (extend r)
      )
    return (Map.singleton x $ extend r, ty)
  Nothing ->
    throwError ("unknown identifier: " ++ render (iPrint 0 0 $ Free x))
-- App:
iType ii g r (e1 :@: e2) = do
  (qs1, si) <- iType ii g r e1
  case si of
    VPi p ty ty' -> do
      let r' = extend r
      qs <- if p S.* r' == Zero
        then do
          _ <- cType ii g Rig0' e2 ty
          return qs1
        else do
          qs2 <- cType ii g Rig1' e2 ty
          return $ Map.unionWith (S.+) qs1 (Map.map (p S.* r' S.*) qs2)
      return (qs, ty' $ cEval e2 (fst g, []))
    _ -> throwError "illegal application"
-- PairElim:
iType ii g r (PairElim l i t) = do
  (qs1, lty) <- iType ii g r l
  case lty of
    z@(VTensPr p ty ty') -> do
      let r' = extend r
      let local_g = second
            ([ Binding (Local ii)       (p S.* r') ty
             , Binding (Local $ ii + 1) r'         (ty' . vfree $ Local ii)
             ] ++
            )
            g
      let
        txy = cSubst
          0
          (Ann (Pair (Inf . Free $ Local ii) (Inf . Free $ Local (ii + 1)))
               (quote0 z)
          )
          t
      qs3 <- cType (ii + 2) (second forget local_g) Rig0' txy VStar
      let txyVal = cEval txy (fst local_g, [])
      qs2 <- cType
        (ii + 2)
        local_g
        r
        (cSubst 1 (Free $ Local ii) . cSubst 0 (Free $ Local (ii + 1)) $ i)
        txyVal
      let qs = Map.unionsWith (S.+) [qs1, qs2, qs3]
      qs'  <- checkLocal "pairElim, Local ii" ii qs (p S.* r') (snd local_g)
      qs'' <- checkLocal "pairElim, Local ii+1" (ii + 1) qs' r' (snd local_g)
      let tl = cEval (cSubst 0 l t) (fst local_g, [])
      return (qs'', tl)
    _ -> throwError "illegal pair elimination"
-- UnitElim:
iType ii g r (UnitElim l i t) = do
  (qs1, lty) <- iType ii g r l
  case lty of
    VUnitType -> do
      let local_g = second (forget . (Binding (Local ii) Zero VUnitType :)) g
      let tu      = cSubst 0 (Ann Unit UnitType) t
      qs3 <- cType (ii + 1) local_g Rig0' tu VStar
      let tuVal = cEval tu (fst g, [])
      qs2 <- cType ii g r i tuVal
      let qs = Map.unionsWith (S.+) [qs1, qs2, qs3]
      let tl = cEval (cSubst 0 l t) (fst g, [])
      return (qs, tl)
    _ -> throwError "illegal unit elimination"
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
    ++ render (cPrint 0 0 $ quote0 v')
    ++ "\n"
    ++ "type expected:  "
    ++ render (cPrint 0 0 $ quote0 v)
    ++ "\n"
    ++ "for expression: "
    ++ render (iPrint 0 0 e)
    )
  return qs
-- Lam:
cType ii g r (Lam e) (VPi p ty ty') = do
  let iiq     = p S.* extend r
  let local_g = second (Binding (Local ii) iiq ty :) g
  qs <- cType (ii + 1)
              local_g
              r
              (cSubst 0 (Free $ Local ii) e)
              (ty' . vfree $ Local ii)
  checkLocal "lam" ii qs iiq (snd local_g)
-- Star:
cType _  _ _     Star            VStar = return Map.empty
-- Fun:
cType ii g Rig0' (Pi _ tyt tyt') VStar = do
  _ <- cType ii (second forget g) Rig0' tyt VStar
  let ty      = cEval tyt (fst g, [])
  let local_g = second (forget . (Binding (Local ii) Zero ty :)) g
  qs <- cType (ii + 1) local_g Rig0' (cSubst 0 (Free $ Local ii) tyt') VStar
  checkLocal "fun" ii qs Zero (snd local_g)
-- Pair:
cType ii g r (Pair e1 e2) (VTensPr p ty ty') = do
  let r' = extend r
  qs <- if p S.* r' == Zero
    then do
      _ <- cType ii g Rig0' e1 ty
      rest
    else do
      qs1 <- cType ii g Rig1' e1 ty
      qs2 <- rest
      return $ Map.unionWith (S.+) qs2 (Map.map (p S.* r' S.*) qs1)
  checkLocal "pair" ii qs p (snd g)
 where
  rest = do
    let e1v = cEval e1 (fst g, [])
    cType ii g r e2 (ty' e1v)
-- TensPr:
cType ii g Rig0' (TensPr _ tyt tyt') VStar = do
  _ <- cType ii (second forget g) Rig0' tyt VStar
  let ty      = cEval tyt (fst g, [])
  let local_g = second (forget . (Binding (Local ii) Zero ty :)) g
  qs <- cType (ii + 1) local_g Rig0' (cSubst 0 (Free $ Local ii) tyt') VStar
  checkLocal "tensPr" ii qs Zero (snd local_g)
-- Unit:
cType _ _ _ Unit     VUnitType = return Map.empty
-- UnitType:
cType _ _ _ UnitType VStar     = return Map.empty
cType _ _ _ _        _         = throwError "type mismatch (cType)"

checkLocal :: String -> Int -> Usage -> ZeroOneMany -> Context -> Result Usage
checkLocal d ii qs r ctx = do
  let (q, qs') = splitLocal ii qs
  unless
    (q <: r)
    (  throwError
    $  "unavailable resources ("
    ++ d
    ++ "):\n"
    ++ "  for variable Local "
    ++ show ii
    ++ " : used: "
    ++ show q
    ++ ", available: "
    ++ show r
    ++ "\n"
    ++ err qs ctx
    )
  return qs'
 where
  splitLocal :: Int -> Usage -> (ZeroOneMany, Usage)
  splitLocal ii' = first (fromMaybe Zero) . Map.alterF (, Nothing) (Local ii')

err :: Usage -> Context -> String
err qs ctx =
  "  context: " ++ show ctx ++ "\n     used: " ++ show (Map.toList qs)

