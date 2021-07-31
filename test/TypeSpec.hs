module TypeSpec
  ( spec
  ) where

import           Control.Applicative            ( liftA3 )
import           Control.Monad.Except           ( throwError )
import           Data.Function                  ( on )
import           Janus.Evaluation
import           Janus.Infer
import           Janus.Judgment
import           Janus.Pretty
import           Janus.Semiring
import           Janus.Syntax
import           Test.Hspec

data TestCase = TestCase
  { desc  :: String
  , ctx   :: (ValueEnv, Context)
  , multi :: ZeroOneMany
  , expr  :: ITerm
  , res   :: TestResult
  }

newtype TestResult =  TestResult (Result CTerm)

instance Eq TestResult where
  (TestResult (Left te)) == (TestResult (Left te')) =
    ((==) `on` (renderString . pretty)) te te'
  (TestResult (Right ty)) == (TestResult (Right ty')) = ty == ty'
  _                       == _                        = False

instance Show TestResult where
  show (TestResult (Left  te)) = renderString $ pretty te
  show (TestResult (Right ty)) = show ty

spec :: Spec
spec = mapM_ run cases
 where
  run tc =
    it (desc tc)
      $          TestResult (quote0 <$> liftA3 synthesise ctx multi expr tc)
      `shouldBe` res tc

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
    (TestResult . return $ ifg "a")
  , TestCase
    "Constant function application"
    -- 1 ((λa b x y. x)
    -- : ∀ (0 a : U) (0 b : (0 _ : a) -> U) (1 x : a) (w y : b x) . a) a (\a. b) x y
    ( []
    , [ Binding (Global "a") Zero VUniverse
      , Binding (Global "b") Zero VUniverse
      , Binding (Global "x") One  (vfree $ Global "a")
      , Binding (Global "y") Many (vfree $ Global "b")
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
    (TestResult . return $ ifg "a")
  , TestCase
    "Second projection of dependent multiplicative pair"
    -- 1 let 1 _ @ x, y = (a, x) : (0 _ : U) * a in y : a
    abxyContext
    One
    (MPairElim
      One
      (Ann (MPair (ifg "a") (ifg "x")) (MPairType Zero Universe (ifg "a")))
      (ib 0)
      (ifg "a")
    )
    (TestResult . return $ ifg "a")
  , TestCase
    "Linear swap"
    -- 1 ((\p. let 1 z @ x, y = p in (y, x) : (1 _ : b) * a) : (1 _ : (1 _ : a) * b) -> (1 _ : b) * a) (x, y)
    abxyContext
    One
    (   Ann
        (Lam
          (Inf
            (MPairElim One
                       (Bound 0)
                       (MPair (ib 0) (ib 1))
                       (MPairType One (ifg "b") (ifg "a"))
            )
          )
        )
        (Pi One
            (MPairType One (ifg "a") (ifg "b"))
            (MPairType One (ifg "b") (ifg "a"))
        )
    :$: MPair (ifg "x") (ifg "y")
    )
    (TestResult . return $ MPairType One (ifg "b") (ifg "a"))
  , TestCase
    "Second projection of dependent additive pair"
    -- 1 ((\p. snd p) : (1 _ : (_ : a) & b) -> b) <x, y>
    abxyContext
    One
    (   Ann (Lam (Inf (Snd (Bound 0))))
            (Pi One (APairType (ifg "a") (ifg "b")) (ifg "b"))
    :$: APair (ifg "x") (ifg "y")
    )
    (TestResult . throwError $ UsageError
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
      , Binding (Global "x") One  (vfree $ Global "a")
      , Binding (Global "y") One  (vfree $ Global "b")
      ]
    )

