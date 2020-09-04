module TypeSpec
  ( spec
  )
where

import           Test.Hspec
import           Typing
import           Types
import           Control.Monad                  ( foldM )
import           Data.Bifunctor                 ( first
                                                , second
                                                )

data SuccTest = SuccTest String (NameEnv, Context) ZeroOneOmega ITerm CTerm

succTests :: [SuccTest]
succTests =
  [ SuccTest
      "Identity application"
      ( []
      , [ (Global "MyBool" , (Rig0, VStar))
        , (Global "MyFalse", (Rig1, VNeutral . NFree $ Global "MyBool"))
        ]
      )
      Rig1
      (   Ann (Lam . Lam . Inf $ Bound 0)
              (Pi RigW Star $ Pi Rig1 (Inf $ Bound 0) (Inf $ Bound 1))
      :@: (Inf . Free $ Global "MyBool")
      :@: (Inf . Free $ Global "MyFalse")
      )
      (Inf . Free $ Global "MyBool")
  ]

succTestSpec :: SuccTest -> SpecWith ()
succTestSpec (SuccTest d g q i t) =
  it d $ (quote0 <$> iType0 g q i) `shouldBe` Right t

spec :: Spec
spec = describe "Type-checker" $ do
  foldM (const succTestSpec) () succTests

