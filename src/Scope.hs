module Scope where

import           Types

lpte :: Context
lpte =
  [ (Global "Zero", VNat)
  , (Global "Succ", VPi VNat (const VNat))
  , (Global "Nat" , VStar)
  , ( Global "natElim"
    , VPi
      (VPi VNat (const VStar))
      (\m -> VPi
        (m `vapp` VZero)
        (\_ -> VPi
          (VPi VNat (\k -> VPi (m `vapp` k) (\_ -> m `vapp` VSucc k)))
          (\_ -> VPi VNat (m `vapp`))
        )
      )
    )
  , (Global "Nil", VPi VStar (`VVec` VZero))
  , ( Global "Cons"
    , VPi
      VStar
      (\a ->
        VPi VNat (\n -> VPi a (\_ -> VPi (VVec a n) (\_ -> VVec a (VSucc n))))
      )
    )
  , (Global "Vec", VPi VStar (\_ -> VPi VNat (const VStar)))
  , ( Global "vecElim"
    , VPi
      VStar
      (\a -> VPi
        (VPi VNat (\n -> VPi (VVec a n) (const VStar)))
        (\m -> VPi
          (m `vapp` VZero `vapp` VNil a)
          (\_ -> VPi
            (VPi
              VNat
              (\n -> VPi
                a
                (\x -> VPi
                  (VVec a n)
                  (\xs -> VPi (m `vapp` n `vapp` xs)
                              (\_ -> m `vapp` VSucc n `vapp` VCons a n x xs)
                  )
                )
              )
            )
            (\_ -> VPi VNat (\n -> VPi (VVec a n) (\xs -> m `vapp` n `vapp` xs))
            )
          )
        )
      )
    )
  , (Global "Refl", VPi VStar (\a -> VPi a (\x -> VEq a x x)))
  , (Global "Eq"  , VPi VStar (\a -> VPi a (\_ -> VPi a (const VStar))))
  , ( Global "eqElim"
    , VPi
      VStar
      (\a -> VPi
        (VPi a (\x -> VPi a (\y -> VPi (VEq a x y) (const VStar))))
        (\m -> VPi
          (VPi a (\x -> m `vapp` x `vapp` x `vapp` VRefl a x))
          (\_ -> VPi
            a
            (\x -> VPi
              a
              (\y -> VPi (VEq a x y) (\eq -> m `vapp` x `vapp` y `vapp` eq))
            )
          )
        )
      )
    )
  , (Global "FZero", VPi VNat (VFin . VSucc))
  , (Global "FSucc", VPi VNat (\n -> VPi (VFin n) (\_ -> VFin (VSucc n))))
  , (Global "Fin"  , VPi VNat (const VStar))
  , ( Global "finElim"
    , VPi
      (VPi VNat (\n -> VPi (VFin n) (const VStar)))
      (\m -> VPi
        (VPi VNat (\n -> m `vapp` VSucc n `vapp` VFZero n))
        (\_ -> VPi
          (VPi
            VNat
            (\n -> VPi
              (VFin n)
              (\f -> VPi (m `vapp` n `vapp` f)
                         (\_ -> m `vapp` VSucc n `vapp` VFSucc n f)
              )
            )
          )
          (\_ -> VPi VNat (\n -> VPi (VFin n) (\f -> m `vapp` n `vapp` f)))
        )
      )
    )
  ]

lpve :: NameEnv
lpve =
  [ (Global "Zero", VZero)
  , (Global "Succ", VLam VSucc)
  , (Global "Nat" , VNat)
  , ( Global "natElim"
    , cEval
      (Lam
        (Lam
          (Lam
            (Lam
              (Inf
                (NatElim (Inf (Bound 3))
                         (Inf (Bound 2))
                         (Inf (Bound 1))
                         (Inf (Bound 0))
                )
              )
            )
          )
        )
      )
      ([], [])
    )
  , (Global "Nil" , VLam VNil)
  , (Global "Cons", VLam (\a -> VLam (\n -> VLam (VLam . VCons a n))))
  , (Global "Vec" , VLam (VLam . VVec))
  , ( Global "vecElim"
    , cEval
      (Lam
        (Lam
          (Lam
            (Lam
              (Lam
                (Lam
                  (Inf
                    (VecElim (Inf (Bound 5))
                             (Inf (Bound 4))
                             (Inf (Bound 3))
                             (Inf (Bound 2))
                             (Inf (Bound 1))
                             (Inf (Bound 0))
                    )
                  )
                )
              )
            )
          )
        )
      )
      ([], [])
    )
  , (Global "Refl", VLam (VLam . VRefl))
  , (Global "Eq"  , VLam (\a -> VLam (VLam . VEq a)))
  , ( Global "eqElim"
    , cEval
      (Lam
        (Lam
          (Lam
            (Lam
              (Lam
                (Lam
                  (Inf
                    (EqElim (Inf (Bound 5))
                            (Inf (Bound 4))
                            (Inf (Bound 3))
                            (Inf (Bound 2))
                            (Inf (Bound 1))
                            (Inf (Bound 0))
                    )
                  )
                )
              )
            )
          )
        )
      )
      ([], [])
    )
  , (Global "FZero", VLam VFZero)
  , (Global "FSucc", VLam (VLam . VFSucc))
  , (Global "Fin"  , VLam VFin)
  , ( Global "finElim"
    , cEval
      (Lam
        (Lam
          (Lam
            (Lam
              (Lam
                (Inf
                  (FinElim (Inf (Bound 4))
                           (Inf (Bound 3))
                           (Inf (Bound 2))
                           (Inf (Bound 1))
                           (Inf (Bound 0))
                  )
                )
              )
            )
          )
        )
      )
      ([], [])
    )
  ]
