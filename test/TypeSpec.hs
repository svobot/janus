module TypeSpec
  ( spec
  )
where

import           Control.Monad                  ( foldM )
import           Test.Hspec
import           Types
import           Typing

data SuccTest = SuccTest String (NameEnv, Context) ZeroOneMany ITerm CTerm

succTests :: [SuccTest]
succTests =
  [ SuccTest
    "Identity application"
    ( []
    , [ Binding (Global "a") Rig0 VStar
      , Binding (Global "x") Rig1 (VNeutral . NFree $ Global "a")
      ]
    )
    Rig1
    (   Ann (Lam . Lam $ ib 0) (Pi Rig0 Star $ Pi Rig1 (ib 0) (ib 1))
    :@: ifg "a"
    :@: ifg "x"
    )
    (ifg "a")
  , SuccTest
    "Dependent pair snd projection"
    ( []
    , [ Binding (Global "a") Rig0 VStar
      , Binding (Global "x") Rig0 (VNeutral . NFree $ Global "a")
      ]
    )
    Rig0
    -- TODO: Should work too?: (PairElim (Ann (Pair (ifg "a") (ifg "x")) (TensPr Rig0 Star (ib 0)))
    (PairElim (Ann (Pair (ifg "a") (ifg "x")) (TensPr Rig0 Star (ifg "a")))
              (ib 0)
              (ifg "a")
    )
    (ifg "a")
  ]
 where
  fg  = Free . Global
  ifg = Inf . fg
  ib  = Inf . Bound

succTestSpec :: SuccTest -> SpecWith ()
succTestSpec (SuccTest d g q i t) =
  it d $ (quote0 <$> iType0 g q i) `shouldBe` Right t

spec :: Spec
spec = foldM (const succTestSpec) () succTests

