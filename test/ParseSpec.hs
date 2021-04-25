module ParseSpec
  ( spec
  ) where

import           Data.Bifunctor                 ( first )
import           Parser
import           Semiring
import           Test.Hspec
import           Text.Parsec                    ( ParseError )
import           Types

newtype TestResult a = TestResult (Either (Maybe ParseError) a)

instance (Eq a) => Eq (TestResult a) where
  (TestResult (Right x)) == (TestResult (Right y)) = x == y
  (TestResult (Left  _)) == (TestResult (Left  _)) = True
  _                      == _                      = False

instance (Show a) => Show (TestResult a) where
  show (TestResult x) = either (maybe "Parse error" show) show x

success :: a -> TestResult a
success = TestResult . return

err :: TestResult a
err = TestResult $ Left Nothing

data TestCase a = TestCase
  { desc :: String
  , expr :: String
  , res  :: TestResult a
  }

spec :: Spec
spec = do
  describe "Statement" $ mapM_ (run evalParser) stmtCases
  describe "File" $ mapM_ (run $ fileParser "<test>") fileCases
 where
  run p tc = it (desc tc) $ val p tc `shouldBe` res tc
  val p tc = TestResult . first Just . p $ expr tc

fg :: String -> ITerm
fg = Free . Global

ifg :: String -> CTerm
ifg = Inf . fg

ib :: Int -> CTerm
ib = Inf . Bound

stmtCases :: [TestCase Stmt]
stmtCases =
  [ TestCase "Left associative function application"
             "f x y"
             (success . Eval Many $ fg "f" :$: ifg "x" :$: ifg "y")
  , TestCase "Annotated function application"
             "f x : a"
             (success . Eval Many $ Ann (Inf $ fg "f" :$: ifg "x") (ifg "a"))
  , TestCase
    "Annotated identity function"
    "\\a x . x : (0 a : U) -> (1 _ : a) -> a"
    (success . Eval Many $ Ann (Lam (Lam (ib 0)))
                               (Pi Zero Universe (Pi One (ib 0) (ib 1)))
    )
  , TestCase
    "Unicode identity function application"
    "1 (λa x . x : ∀ (0 a : U) (1 _ : a) . a) a x"
    (   success
    .   Eval One
    $   Ann (Lam (Lam (ib 0))) (Pi Zero Universe (Pi One (ib 0) (ib 1)))
    :$: ifg "a"
    :$: ifg "x"
    )
  , TestCase
    "Assumption"
    "assume (0 a : U) (1 x : a) (many : U)"
    (success $ Assume
      [ Binding "a"    Zero Universe
      , Binding "x"    One  (ifg "a")
      , Binding "many" Many Universe
      ]
    )
  , TestCase
    "Multiplicative pair elimination"
    (unlines
      [ "let p @ x', y' = (x, f y z) : (0 x : a) * x in y'"
      , "               : ((λu . a) : (0 _ : (0 z : U) * z) -> U) p"
      ]
    )
    (success . Eval Many $ PairElim
      (Ann (Pair (ifg "x") (Inf $ fg "f" :$: ifg "y" :$: ifg "z"))
           (Tensor Zero (ifg "a") (ib 0))
      )
      (ib 0)
      (Inf
        (   Ann (Lam (ifg "a")) (Pi Zero (Tensor Zero Universe (ib 0)) Universe)
        :$: ib 0
        )
      )
    )
  , TestCase
    "Multiplicative unit elimination"
    "0 let u @ () = f x in y : g u"
    (success . Eval Zero $ MUnitElim (fg "f" :$: ifg "x")
                                     (ifg "y")
                                     (Inf $ fg "g" :$: ib 0)
    )
  , TestCase
    "Additive pair"
    "let p = <x, f y> : (x : a) & f x"
    (success . Let Many "p" $ Ann
      (Angles (ifg "x") (Inf $ fg "f" :$: ifg "y"))
      (With (ifg "a") (Inf $ fg "f" :$: ib 0))
    )
  , TestCase
    "Additive pair elimination"
    "1 λp. (fst p, snd p) : ∀ (p : (_ : a) & b) . (_ : a) * b"
    (success . Eval One $ Ann
      (Lam (Pair (Inf (Fst (Bound 0))) (Inf (Snd (Bound 0)))))
      (Pi Many (With (ifg "a") (ifg "b")) (Tensor Many (ifg "a") (ifg "b")))
    )
  , TestCase
    "Units"
    "(\\m a. m : forall (1 _ : I) (0 _ : T) . I) () <>"
    (   success
    .   Eval Many
    $   (Ann (Lam (Lam (ib 1))) (Pi One MUnitType (Pi Zero AUnitType MUnitType))
        :$: MUnit
        )
    :$: AUnit
    )
  , TestCase
    "Plentiful parentheses"
    (unlines
      [ "1 ((\\x y. ((x) : I))"
      , "  : forall (1 _ : ((I)))"
      , "    (_ : ((_ : (I)) * T))"
      , "  . (I)) ((())) (((), <>))"
      ]
    )
    (   success
    .   Eval One
    $   (   Ann
            (Lam (Lam (Inf (Ann (ib 1) MUnitType))))
            (Pi One
                MUnitType
                (Pi Many (Tensor Many MUnitType AUnitType) MUnitType)
            )
        :$: MUnit
        )
    :$: Pair MUnit AUnit
    )
  , TestCase "Missing parenthesis" "f : (1 _ : a) -> U x" err
  , TestCase
    "Annotated Pi type"
    "0 (0 x : a) -> b : U"
    (success . Eval Zero $ Ann (Pi Zero (ifg "a") (ifg "b")) Universe)
  , TestCase
    "Annotated Pi type in parentheses"
    "0 ((0 x : a) -> b) : U"
    (success . Eval Zero $ Ann (Pi Zero (ifg "a") (ifg "b")) Universe)
  , TestCase
    "Annotated Tensor type"
    "0 (0 x : a) * b : U"
    (success . Eval Zero $ Ann (Tensor Zero (ifg "a") (ifg "b")) Universe)
  , TestCase
    "Annotated Tensor type in parentheses"
    "0 ((0 x : a) * b) : U"
    (success . Eval Zero $ Ann (Tensor Zero (ifg "a") (ifg "b")) Universe)
  , TestCase "Annotated With type"
             "0 (x : a) & b : U"
             (success . Eval Zero $ Ann (With (ifg "a") (ifg "b")) Universe)
  , TestCase "Annotated With type in parentheses"
             "0 ((x : a) & b) : U"
             (success . Eval Zero $ Ann (With (ifg "a") (ifg "b")) Universe)
  ]

fileCases :: [TestCase [Stmt]]
fileCases =
  [ TestCase
      "Two lets"
      (unlines
        [ "let 1 v = let _ @ x,y = p in x : a"
        , ""
        , "let u = let _ @ () = () : I in x : a"
        ]
      )
      (success
        [ Let One "v" $ PairElim (fg "p") (ib 1) (ifg "a")
        , Let Many "u" $ MUnitElim (Ann MUnit MUnitType) (ifg "x") (ifg "a")
        ]
      )
  ]

