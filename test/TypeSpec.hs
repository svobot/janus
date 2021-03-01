module TypeSpec
  ( spec
  ) where

import           Control.Applicative            ( liftA3 )
import           Control.Monad.Except           ( throwError )
import           Rig
import           Test.Hspec
import           Types
import           Typing

data TestCase = TestCase
  { desc  :: String
  , ctx   :: Context
  , multi :: ZeroOneMany
  , expr  :: ITerm
  , res   :: TestResult
  }

newtype TestResult =  TR (Result CTerm)

instance Eq TestResult where
  (TR (Left  te)) == (TR (Left  te')) = show te == show te'
  (TR (Right ty)) == (TR (Right ty')) = ty == ty'
  _               == _                = False

instance Show TestResult where
  show (TR (Left  te)) = show te
  show (TR (Right ty)) = show ty

cases :: [TestCase]
cases =
  [ TestCase
    "Identity function application"
    -- 1 (λa x. x : ∀ (0 a : U) (1 _ : a) . a) a x
    abxyContext
    One
    (   Ann (Lam . Lam $ ib 0) (Pi Zero Universe $ Pi One (ib 0) (ib 1))
    :$: ifg "a"
    :$: ifg "x"
    )
    (TR . return $ ifg "a")
  , TestCase
    "Constant function application"
    -- 1 ((λa b x y. x)
    -- : ∀ (0 a : U) (0 b : (0 _ : a) -> U) (1 x : a) (w y : b x) . a) a (\a. b) x y
    ( []
    , [ Binding (Global "a") Zero VUniverse
      , Binding (Global "b") Zero VUniverse
      , Binding (Global "x") One  (VNeutral . NFree $ Global "a")
      , Binding (Global "y") Many (VNeutral . NFree $ Global "b")
      ]
    )
    One
    (   (   (   (   Ann
                    (Lam (Lam (Lam (Lam (ib 1)))))
                    (Pi
                      Zero
                      Universe
                      (Pi Zero
                          (Pi Zero (ib 0) Universe)
                          (Pi One (ib 1) (Pi Many (Inf (Bound 1 :$: ib 0)) (ib 3)))
                      )
                    )
                :$: ifg "a"
                )
            :$: Lam (ifg "b")
            )
        :$: ifg "x"
        )
    :$: ifg "y"
    )
    (TR . return $ ifg "a")
  , TestCase
    "Second projection of dependent multiplicative pair"
    -- 1 let _ @ x, y = (a, x) : (0 _ : U) * a in y : a
    abxyContext
    One
    (PairElim
      (Ann (Pair (ifg "a") (ifg "x")) (Tensor Zero Universe (ifg "a")))
      (ib 0)
      (ifg "a")
    )
    (TR . return $ ifg "a")
  , TestCase
    "Linear swap"
    -- 1 ((\p. let z @ x, y = p in (y, x) : (1 _ : b) * a) : (1 _ : (1 _ : a) * b) -> (1 _ : b) * a) (x, y)
    abxyContext
    One
    (   Ann
        (Lam
          (Inf
            (PairElim (Bound 0)
                      (Pair (ib 0) (ib 1))
                      (Tensor One (ifg "b") (ifg "a"))
            )
          )
        )
        (Pi One
            (Tensor One (ifg "a") (ifg "b"))
            (Tensor One (ifg "b") (ifg "a"))
        )
    :$: Pair (ifg "x") (ifg "y")
    )
    (TR . return $ Tensor One (ifg "b") (ifg "a"))
  , TestCase
    "Second projection of dependent additive pair"
    -- 1 ((\p. snd p) : (1 _ : (_ : a) & b) -> b) <x, y>
    abxyContext
    One
    (   Ann (Lam (Inf (Snd (Bound 0))))
            (Pi One (With (ifg "a") (ifg "b")) (ifg "b"))
    :$: Angles (ifg "x") (ifg "y")
    )
    (TR . throwError $ MultiplicityError
      Nothing
      [ (Global "x", vfree $ Global "a", Many, One)
      , (Global "y", vfree $ Global "b", Many, One)
      ]
    )
  ]
 where
  fg  = Free . Global
  ifg = Inf . fg
  ib  = Inf . Bound

  abxyContext =
    ( []
    , [ Binding (Global "a") Zero VUniverse
      , Binding (Global "b") Zero VUniverse
      , Binding (Global "x") One  (VNeutral . NFree $ Global "a")
      , Binding (Global "y") One  (VNeutral . NFree $ Global "b")
      ]
    )
run :: TestCase -> Spec
run tc =
  it (desc tc)
    $          TR (quote0 <$> liftA3 iType0 ctx multi expr tc)
    `shouldBe` res tc

spec :: Spec
spec = mapM_ run cases

