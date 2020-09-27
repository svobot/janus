module TypeSpec
  ( spec
  )
where

import           Test.Hspec
import           Typing
import           Types
import           Control.Monad                  ( foldM )

data SuccTest = SuccTest String (NameEnv, Context) ZeroOneOmega ITerm CTerm

succTests :: [SuccTest]
succTests =
  [ SuccTest
    "Identity application"
    ( []
    , [ (Global "a", (Rig0, VStar))
      , (Global "x", (Rig1, VNeutral . NFree $ Global "a"))
      ]
    )
    Rig1
    (   Ann
        (Lam . Lam $ ib 0)
        ( Pi Rig0 {- TODO: shold RigW work too? -}Star
        $ Pi Rig1 (ib 0) (ib 1)
        )
    :@: ifg "a"
    :@: ifg "x"
    )
    (ifg "a")
  , SuccTest
    " Dependent pair snd projection"
    ( []
    , [ (Global "a", (Rig0, VStar))
      , (Global "x", (Rig1, VNeutral . NFree $ Global "a"))
      ]
    )
    Rig1
    (Ann
      (PairElim (Ann (Pair (ifg "a") (ifg "x")) (TensPr Rig0 Star (ib 0)))
                (ib 0)
      )
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

