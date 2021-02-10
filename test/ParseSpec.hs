module ParseSpec
  ( spec
  ) where

import           Data.Bifunctor                 ( first )
import           Parser
import           Rig
import           Test.Hspec
import           Text.Parsec                    ( ParseError
                                                , eof
                                                , many
                                                , parse
                                                )
import           Text.Parsec.String             ( GenParser )
import           Text.Parsec.Token              ( whiteSpace )
import           Types

newtype TestResult a = TR (Either (Maybe ParseError) a)

instance (Eq a) => Eq (TestResult a) where
  (TR (Right x)) == (TR (Right y)) = x == y
  (TR (Left  _)) == (TR (Left  _)) = True
  _              == _              = False

instance (Show a) => Show (TestResult a) where
  show (TR x) = either (maybe "Parse error" show) show x

success :: a -> TestResult a
success = TR . return

err :: TestResult a
err = TR $ Left Nothing

data TestCase a = TestCase
  { desc :: String
  , expr :: String
  , res  :: TestResult a
  }

type CharParser = GenParser Char ()

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
    "1 λp. (Fst p, Snd p) : ∀ (p : (_ : a) & b) . (_ : a) * b"
    (success . Eval One $ Ann
      (Lam (Pair (Inf (Fst (Bound 0))) (Inf (Snd (Bound 0)))))
      (Pi Many (With (ifg "a") (ifg "b")) (Tensor Many (ifg "a") (ifg "b")))
    )
  , TestCase
    "Units"
    "(\\m a. m : forall (1 _ : MUnit) (0 _ : AUnit) . MUnit) () <>"
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
      [ "1 ((\\x y. ((x) : MUnit))"
      , "  : forall (1 _ : ((MUnit)))"
      , "    (_ : ((_ : (MUnit)) * AUnit))"
      , "  . (MUnit)) ((())) (((), <>))"
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
  ]

fileCases :: [TestCase [Stmt]]
fileCases =
  [ TestCase
      "Two lets"
      (unlines
        [ "let 1 v = let _ @ x,y = p in x : a"
        , ""
        , "let u = let _ @ () = () : MUnit in x : a"
        ]
      )
      (success
        [ Let One "v" $ PairElim (fg "p") (ib 1) (ifg "a")
        , Let Many "u" $ MUnitElim (Ann MUnit MUnitType) (ifg "x") (ifg "a")
        ]
      )
  ]

run :: (Eq a, Show a) => CharParser a -> TestCase a -> SpecWith ()
run p tc = it (desc tc) $ val `shouldBe` res tc
 where
  val = TR . first Just . parse p' "<test>" $ expr tc
  p'  = whiteSpace lang *> p <* eof

spec :: Spec
spec = do
  describe "Statement" $ mapM_ (run stmt) stmtCases
  describe "File" $ mapM_ (run $ many stmt) fileCases

