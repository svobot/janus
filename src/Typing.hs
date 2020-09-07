{-# LANGUAGE LambdaCase #-}

module Typing where

import           Control.Monad                  ( unless )
import           Control.Monad.Except           ( throwError )
import           Control.Monad.Trans            ( liftIO )
import           Data.Bifunctor                 ( second )
import qualified Data.Map.Strict               as Map
import           Types
import           Printer
import           Text.PrettyPrint               ( render )

import           Debug.Trace

data ZeroOne = Rig0' | Rig1' deriving (Eq)

instance Show ZeroOne where
  show Rig0' = "0"
  show Rig1' = "1"

restrict :: ZeroOneOmega -> ZeroOne
restrict Rig0 = Rig0'
restrict Rig1 = Rig1'
restrict RigW = Rig1'

extend :: ZeroOne -> ZeroOneOmega
extend Rig0' = Rig0
extend Rig1' = Rig1

type Usage = Map.Map Name ZeroOneOmega

iinfer :: (NameEnv, Context) -> ZeroOneOmega -> ITerm -> Repl (Maybe Type)
iinfer g r t = case iType0 g r t of
  Left  e -> liftIO $ putStrLn e >> return Nothing
  Right v -> return (Just v)

iType0 :: (NameEnv, Context) -> ZeroOneOmega -> ITerm -> Result Type
iType0 g r t = do
  let r' = restrict r
  (qs', tp) <- iType 0 g r' t
  let qs = Map.map (rigMult r) qs'
  unless (qs `fits` snd g)
         (throwError $ "unavailable resources:\n" ++ rs qs (snd g))
  traceM ("typing output:\n" ++ rs qs (snd g))
  return tp

rs qs ctx = " context: " ++ show ctx ++ "\n used:    " ++ show qs

iType :: Int -> (NameEnv, Context) -> ZeroOne -> ITerm -> Result (Usage, Type)
-- Cut:
iType ii g r (Ann e tyt) = do
  _ <- cType ii (second forget g) Rig0' tyt VStar
  let ty = cEval tyt (fst g, [])
  qs <- cType ii g r e ty
  return (qs, ty)
-- Var:
iType _ g r (Free x) = case lookup x (snd g) of
  Just (q, ty) -> do
    traceM
      (  "var "
      ++ show x
      ++ ": "
      ++ show q
      ++ " in context, "
      ++ show r
      ++ " used"
      )
    return (Map.singleton x q, ty)
  Nothing ->
    throwError ("unknown identifier: " ++ render (iPrint 0 0 $ Free x))
-- App:
iType ii g r (e1 :@: e2) = do
  (qs1, si) <- iType ii g r e1
  case si of
    VPi p ty ty' -> do
      let r' = extend r
      qs <- if p `rigMult` r' == Rig0
        then do
          _ <- cType ii g Rig0' e2 ty
          return qs1
        else do
          qs2 <- cType ii g Rig1' e2 ty
          return $ Map.unionWith rigMult
                                 qs1
                                 (Map.map (rigMult $ p `rigMult` r') qs2)
      return (qs, ty' $ cEval e2 (fst g, []))
    _ -> throwError "illegal application"
iType _ _ _ _ = throwError "type mismatch (iType)"

cType :: Int -> (NameEnv, Context) -> ZeroOne -> CTerm -> Type -> Result Usage
-- Elim
cType ii g r (Inf e) v = do
  (qs, v') <- iType ii g r e
  unless
    (quote0 v == quote0 v')
    (throwError
      (  "type mismatch:\n"
      ++ "type inferred:  "
      ++ render (cPrint 0 0 $ quote0 v')
      ++ "\n"
      ++ "type expected:  "
      ++ render (cPrint 0 0 $ quote0 v)
      ++ "\n"
      ++ "for expression: "
      ++ render (iPrint 0 0 e)
      )
    )
  return qs
-- Lam:
cType ii g r (Lam e) (VPi p ty ty') = do
  let iiq     = p `rigMult` extend r
  let local_g = second ((Local ii, (iiq, ty)) :) g
  qs <- cType (ii + 1)
              local_g
              r
              (cSubst 0 (Free $ Local ii) e)
              (ty' . vfree $ Local ii)
  let (q, qs') = splitLocal ii qs
  unless
    (q `rigLess` iiq)
    (throwError $ "unavailable resources (lam):\n" ++ rs qs (snd local_g))
  return qs'
-- Star:
cType _  _ _     Star            VStar = return Map.empty
-- Fun:
cType ii g Rig0' (Pi _ tyt tyt') VStar = do
  _ <- cType ii (second forget g) Rig0' tyt VStar
  let ty      = cEval tyt (fst g, [])
  let local_g = second (forget . ((Local ii, (Rig0, ty)) :)) g
  qs <- cType (ii + 1) local_g Rig0' (cSubst 0 (Free $ Local ii) tyt') VStar
  let (q, qs') = splitLocal ii qs
  unless
    (q `rigLess` Rig0)
    (throwError $ "unavailable resources (fun):\n" ++ rs qs (snd local_g))
  return qs'
cType _ _ _ _ _ = throwError "type mismatch (cType)"

splitLocal :: Int -> Usage -> (ZeroOneOmega, Usage)
splitLocal ii = Map.alterF
  (\case
    Nothing -> error $ show (Local ii) ++ " not found in the usages."
    Just a  -> (a, Nothing)
  )
  (Local ii)

fits :: Usage -> Context -> Bool
fits qs ctx =
  all
      (\(n, q) -> case lookup n ctx of
        Just (q', _) -> q `rigLess` q'
        Nothing      -> False
      )
    $ Map.toList qs

