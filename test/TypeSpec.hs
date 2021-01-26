module TypeSpec
  ( spec
  ) where

import           Data.Bifunctor                 ( first )
import           Data.Text                      ( unpack )
import           Data.Text.Prettyprint.Doc      ( hardline
                                                , nest
                                                )
import           Printer
import           Rig
import           Test.Hspec
import           Types
import           Typing

data SuccTest = SuccTest String (NameEnv, Context) ZeroOneMany ITerm CTerm

succTests :: [SuccTest]
succTests =
  [ SuccTest
    "Identity application"
    ( []
    , [ Binding (Global "a") Zero VUniverse
      , Binding (Global "x") One  (VNeutral . NFree $ Global "a")
      ]
    )
    One
    (   Ann (Lam . Lam $ ib 0) (Pi Zero Universe $ Pi One (ib 0) (ib 1))
    :$: ifg "a"
    :$: ifg "x"
    )
    (ifg "a")
  , SuccTest
    "Dependent pair snd projection"
    ( []
    , [ Binding (Global "a") Zero VUniverse
      , Binding (Global "x") Zero (VNeutral . NFree $ Global "a")
      ]
    )
    Zero
    (PairElim
      (Ann (Pair (ifg "a") (ifg "x")) (Tensor Zero Universe (ifg "a")))
      (ib 0)
      (ifg "a")
    )
    (ifg "a")
  , SuccTest
    "Additive value duplication"
    ( []
    , [ Binding (Global "a") Zero VUniverse
      , Binding (Global "x") Zero (VNeutral . NFree $ Global "a")
      ]
    )
    One
    (Ann
      (Lam (Pair (Inf (Fst (Bound 0))) (Inf (Snd (Bound 0)))))
      (Pi Many
          (With (Inf (Free (Global "a"))) (Inf (Free (Global "a"))))
          (Tensor One (Inf (Free (Global "a"))) (Inf (Free (Global "a"))))
      )
    )
    (Pi Many
        (With (Inf (Free (Global "a"))) (Inf (Free (Global "a"))))
        (Tensor One (Inf (Free (Global "a"))) (Inf (Free (Global "a"))))
    )
  ]
 where
  fg  = Free . Global
  ifg = Inf . fg
  ib  = Inf . Bound

succTestSpec :: SuccTest -> SpecWith ()
succTestSpec (SuccTest d g q i t) =
  it
      (   (d <>)
      .   unpack
      .   render
      .   nest 4
      $   hardline
      <>  prettyAnsi q
      <+> prettyAnsi (Ann (Inf i) t)
      )
    $          first (render . prettyAnsi) (quote0 <$> iType0 g q i)
    `shouldBe` Right t

spec :: Spec
spec = mapM_ succTestSpec succTests

