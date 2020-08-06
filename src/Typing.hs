module Typing where

import           Control.Monad                  ( unless )
import           Control.Monad.Except           ( throwError )
import           Control.Monad.Trans            ( liftIO )
import           Data.Bifunctor                 ( second )
import           Types
import           Printer
import           Text.PrettyPrint               ( render )

iinfer :: NameEnv -> Context -> ITerm -> Repl (Maybe Type)
iinfer d g t = case iType0 (d, g) t of
  Left  e -> liftIO $ putStrLn e >> return Nothing
  Right v -> return (Just v)

iType0 :: (NameEnv, Context) -> ITerm -> Result Type
iType0 = iType 0

iType :: Int -> (NameEnv, Context) -> ITerm -> Result Type
iType ii g (Ann e tyt) = do
  cType ii g tyt VStar
  let ty = cEval tyt (fst g, [])
  cType ii g e ty
  return ty
iType _  _ Star          = return VStar
iType ii g (Pi tyt tyt') = do
  cType ii g tyt VStar
  let ty = cEval tyt (fst g, [])
  cType (ii + 1)
        (second ((:) (Local ii, ty)) g)
        (cSubst 0 (Free (Local ii)) tyt')
        VStar
  return VStar
iType _ g (Free x) = case lookup x (snd g) of
  Just ty -> return ty
  Nothing ->
    throwError ("unknown identifier: " ++ render (iPrint 0 0 (Free x)))
iType ii g (e1 :@: e2) = do
  si <- iType ii g e1
  case si of
    VPi ty ty' -> do
      cType ii g e2 ty
      return (ty' (cEval e2 (fst g, [])))
    _ -> throwError "illegal application"
iType _  _ Nat                 = return VStar
iType ii g (NatElim m mz ms n) = do
  cType ii g m (VPi VNat (const VStar))
  let mVal = cEval m (fst g, [])
  cType ii g mz (mVal `vapp` VZero)
  cType ii
        g
        ms
        (VPi VNat (\k -> VPi (mVal `vapp` k) (\_ -> mVal `vapp` VSucc k)))
  cType ii g n VNat
  let nVal = cEval n (fst g, [])
  return (mVal `vapp` nVal)
iType ii g (Vec a n) = do
  cType ii g a VStar
  cType ii g n VNat
  return VStar
iType ii g (VecElim a m mn mc n vs) = do
  cType ii g a VStar
  let aVal = cEval a (fst g, [])
  cType ii g m (VPi VNat (\n -> VPi (VVec aVal n) (const VStar)))
  let mVal = cEval m (fst g, [])
  cType ii g mn (foldl vapp mVal [VZero, VNil aVal])
  cType
    ii
    g
    mc
    (VPi
      VNat
      (\n -> VPi
        aVal
        (\y -> VPi
          (VVec aVal n)
          (\ys -> VPi (foldl vapp mVal [n, ys])
                      (\_ -> foldl vapp mVal [VSucc n, VCons aVal n y ys])
          )
        )
      )
    )
  cType ii g n VNat
  let nVal = cEval n (fst g, [])
  cType ii g vs (VVec aVal nVal)
  let vsVal = cEval vs (fst g, [])
  return (foldl vapp mVal [nVal, vsVal])
iType i g (Eq a x y) = do
  cType i g a VStar
  let aVal = cEval a (fst g, [])
  cType i g x aVal
  cType i g y aVal
  return VStar
iType i g (EqElim a m mr x y eq) = do
  cType i g a VStar
  let aVal = cEval a (fst g, [])
  cType i
        g
        m
        (VPi aVal (\x -> VPi aVal (\y -> VPi (VEq aVal x y) (const VStar))))
  let mVal = cEval m (fst g, [])
  cType i g mr (VPi aVal (\x -> foldl vapp mVal [x, x]))
  cType i g x  aVal
  let xVal = cEval x (fst g, [])
  cType i g y aVal
  let yVal = cEval y (fst g, [])
  cType i g eq (VEq aVal xVal yVal)
  let eqVal = cEval eq (fst g, [])
  return (foldl vapp mVal [xVal, yVal])
iType _ _ _ = throwError "TODO"


cType :: Int -> (NameEnv, Context) -> CTerm -> Type -> Result ()
cType ii g (Inf e) v = do
  v' <- iType ii g e
  unless
    (quote0 v == quote0 v')
    (throwError
      (  "type mismatch:\n"
      ++ "type inferred:  "
      ++ render (cPrint 0 0 (quote0 v'))
      ++ "\n"
      ++ "type expected:  "
      ++ render (cPrint 0 0 (quote0 v))
      ++ "\n"
      ++ "for expression: "
      ++ render (iPrint 0 0 e)
      )
    )
cType ii g (Lam e) (VPi ty ty') = cType (ii + 1)
                                        (second ((:) (Local ii, ty)) g)
                                        (cSubst 0 (Free (Local ii)) e)
                                        (ty' (vfree (Local ii)))
cType _  _ Zero     VNat              = return ()
cType ii g (Succ k) VNat              = cType ii g k VNat
cType ii g (Nil  a) (VVec bVal VZero) = do
  cType ii g a VStar
  let aVal = cEval a (fst g, [])
  unless (quote0 aVal == quote0 bVal) (throwError "type mismatch")
cType ii g (Cons a n x xs) (VVec bVal (VSucc k)) = do
  cType ii g a VStar
  let aVal = cEval a (fst g, [])
  unless (quote0 aVal == quote0 bVal) (throwError "type mismatch")
  cType ii g n VNat
  let nVal = cEval n (fst g, [])
  unless (quote0 nVal == quote0 k) (throwError "number mismatch")
  cType ii g x  aVal
  cType ii g xs (VVec bVal k)
cType ii g (Refl a z) (VEq bVal xVal yVal) = do
  cType ii g a VStar
  let aVal = cEval a (fst g, [])
  unless (quote0 aVal == quote0 bVal) (throwError "type mismatch")
  cType ii g z aVal
  let zVal = cEval z (fst g, [])
  unless (quote0 zVal == quote0 xVal && quote0 zVal == quote0 yVal)
         (throwError "type mismatch")
cType _ _ _ _ = throwError "type mismatch"
