module TypeSpec
  ( spec
  ) where

import           Control.Applicative            ( liftA3 )
import           Rig
import           Test.Hspec
import           Types
import           Typing

data TestCase = TestCase
  { desc  :: String
  , ctx   :: Context
  , multi :: ZeroOneMany
  , expr  :: ITerm
  , res   :: Result CTerm
  }

defaultContext =
  ( []
  , [ Binding (Global "a") Zero VUniverse
    , Binding (Global "x") One  (VNeutral . NFree $ Global "a")
    ]
  )

testCases :: [TestCase]
testCases =
  [ TestCase
    "Identity application"
    defaultContext
    One
    (   Ann (Lam . Lam $ ib 0) (Pi Zero Universe $ Pi One (ib 0) (ib 1))
    :$: ifg "a"
    :$: ifg "x"
    )
    (Right $ ifg "a")
  , TestCase
    "Dependent pair snd projection"
    defaultContext
    One
    (PairElim
      (Ann (Pair (ifg "a") (ifg "x")) (Tensor Zero Universe (ifg "a")))
      (ib 0)
      (ifg "a")
    )
    (Right $ ifg "a")
  , TestCase
    "Additive value duplication"
    defaultContext
    One
    (Ann
      (Lam (Pair (Inf (Fst (Bound 0))) (Inf (Snd (Bound 0)))))
      (Pi Many
          (With (Inf (Free (Global "a"))) (Inf (Free (Global "a"))))
          (Tensor One (Inf (Free (Global "a"))) (Inf (Free (Global "a"))))
      )
    )
    (Right $ Pi
      Many
      (With (Inf (Free (Global "a"))) (Inf (Free (Global "a"))))
      (Tensor One (Inf (Free (Global "a"))) (Inf (Free (Global "a"))))
    )
  ]
 where
  fg  = Free . Global
  ifg = Inf . fg
  ib  = Inf . Bound

runTestCase :: TestCase -> Spec
runTestCase tc =
  it (desc tc) $ quote0 <$> liftA3 iType0 ctx multi expr tc `shouldBe` res tc

spec :: Spec
spec = mapM_ runTestCase testCases

