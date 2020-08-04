module Typing where

import           Control.Monad                  ( unless )
import           Control.Monad.Except           ( throwError )
import           Control.Monad.Trans            ( liftIO )
import           Data.Bifunctor                 ( second )
import           Types
import           Printer
import           Text.PrettyPrint               ( render )

iinfer :: NameEnv Value -> Context -> ITerm -> Repl (Maybe Type)
iinfer d g t = case iType0_ (d, g) t of
  Left  e -> liftIO $ putStrLn e >> return Nothing
  Right v -> return (Just v)

iType0_ :: (NameEnv Value, Context) -> ITerm -> Result Type
iType0_ = iType_ 0

iType_ :: Int -> (NameEnv Value, Context) -> ITerm -> Result Type
iType_ ii g (Ann e tyt) = do
  cType_ ii g tyt VStar
  let ty = cEval_ tyt (fst g, [])
  cType_ ii g e ty
  return ty
iType_ _  _ Star          = return VStar
iType_ ii g (Pi tyt tyt') = do
  cType_ ii g tyt VStar
  let ty = cEval_ tyt (fst g, [])
  cType_ (ii + 1)
         (second ((:) (Local ii, ty)) g)
         (cSubst_ 0 (Free (Local ii)) tyt')
         VStar
  return VStar
iType_ _ g (Free x) = case lookup x (snd g) of
  Just ty -> return ty
  Nothing ->
    throwError ("unknown identifier: " ++ render (iPrint_ 0 0 (Free x)))
iType_ ii g (e1 :@: e2) = do
  si <- iType_ ii g e1
  case si of
    VPi ty ty' -> do
      cType_ ii g e2 ty
      return (ty' (cEval_ e2 (fst g, [])))
    _ -> throwError "illegal application"
iType_ _  _ Nat                 = return VStar
iType_ ii g (NatElim m mz ms n) = do
  cType_ ii g m (VPi VNat (const VStar))
  let mVal = cEval_ m (fst g, [])
  cType_ ii g mz (mVal `vapp_` VZero)
  cType_ ii
         g
         ms
         (VPi VNat (\k -> VPi (mVal `vapp_` k) (\_ -> mVal `vapp_` VSucc k)))
  cType_ ii g n VNat
  let nVal = cEval_ n (fst g, [])
  return (mVal `vapp_` nVal)
iType_ ii g (Vec a n) = do
  cType_ ii g a VStar
  cType_ ii g n VNat
  return VStar
iType_ ii g (VecElim a m mn mc n vs) = do
  cType_ ii g a VStar
  let aVal = cEval_ a (fst g, [])
  cType_ ii g m (VPi VNat (\n -> VPi (VVec aVal n) (const VStar)))
  let mVal = cEval_ m (fst g, [])
  cType_ ii g mn (foldl vapp_ mVal [VZero, VNil aVal])
  cType_
    ii
    g
    mc
    (VPi
      VNat
      (\n -> VPi
        aVal
        (\y -> VPi
          (VVec aVal n)
          (\ys -> VPi (foldl vapp_ mVal [n, ys])
                      (\_ -> foldl vapp_ mVal [VSucc n, VCons aVal n y ys])
          )
        )
      )
    )
  cType_ ii g n VNat
  let nVal = cEval_ n (fst g, [])
  cType_ ii g vs (VVec aVal nVal)
  let vsVal = cEval_ vs (fst g, [])
  return (foldl vapp_ mVal [nVal, vsVal])
iType_ i g (Eq a x y) = do
  cType_ i g a VStar
  let aVal = cEval_ a (fst g, [])
  cType_ i g x aVal
  cType_ i g y aVal
  return VStar
iType_ i g (EqElim a m mr x y eq) = do
  cType_ i g a VStar
  let aVal = cEval_ a (fst g, [])
  cType_ i
         g
         m
         (VPi aVal (\x -> VPi aVal (\y -> VPi (VEq aVal x y) (const VStar))))
  let mVal = cEval_ m (fst g, [])
  cType_ i g mr (VPi aVal (\x -> foldl vapp_ mVal [x, x]))
  cType_ i g x  aVal
  let xVal = cEval_ x (fst g, [])
  cType_ i g y aVal
  let yVal = cEval_ y (fst g, [])
  cType_ i g eq (VEq aVal xVal yVal)
  let eqVal = cEval_ eq (fst g, [])
  return (foldl vapp_ mVal [xVal, yVal])
iType_ _ _ _ = throwError "TODO"


cType_ :: Int -> (NameEnv Value, Context) -> CTerm -> Type -> Result ()
cType_ ii g (Inf e) v = do
  v' <- iType_ ii g e
  unless
    (quote0_ v == quote0_ v')
    (throwError
      (  "type mismatch:\n"
      ++ "type inferred:  "
      ++ render (cPrint_ 0 0 (quote0_ v'))
      ++ "\n"
      ++ "type expected:  "
      ++ render (cPrint_ 0 0 (quote0_ v))
      ++ "\n"
      ++ "for expression: "
      ++ render (iPrint_ 0 0 e)
      )
    )
cType_ ii g (Lam e) (VPi ty ty') = cType_ (ii + 1)
                                          (second ((:) (Local ii, ty)) g)
                                          (cSubst_ 0 (Free (Local ii)) e)
                                          (ty' (vfree_ (Local ii)))
cType_ _  _ Zero     VNat              = return ()
cType_ ii g (Succ k) VNat              = cType_ ii g k VNat
cType_ ii g (Nil  a) (VVec bVal VZero) = do
  cType_ ii g a VStar
  let aVal = cEval_ a (fst g, [])
  unless (quote0_ aVal == quote0_ bVal) (throwError "type mismatch")
cType_ ii g (Cons a n x xs) (VVec bVal (VSucc k)) = do
  cType_ ii g a VStar
  let aVal = cEval_ a (fst g, [])
  unless (quote0_ aVal == quote0_ bVal) (throwError "type mismatch")
  cType_ ii g n VNat
  let nVal = cEval_ n (fst g, [])
  unless (quote0_ nVal == quote0_ k) (throwError "number mismatch")
  cType_ ii g x  aVal
  cType_ ii g xs (VVec bVal k)
cType_ ii g (Refl a z) (VEq bVal xVal yVal) = do
  cType_ ii g a VStar
  let aVal = cEval_ a (fst g, [])
  unless (quote0_ aVal == quote0_ bVal) (throwError "type mismatch")
  cType_ ii g z aVal
  let zVal = cEval_ z (fst g, [])
  unless (quote0_ zVal == quote0_ xVal && quote0_ zVal == quote0_ yVal)
         (throwError "type mismatch")
cType_ _ _ _ _ = throwError "type mismatch"
