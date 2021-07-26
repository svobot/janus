module ParseSpec
  ( spec
  ) where

import           Data.String                    ( IsString
                                                , fromString
                                                )
import           Data.Void
import           Janus.Judgment
import           Janus.Parsing
import           Janus.Semiring
import           Janus.Syntax
import           Test.Hspec
import           Text.Megaparsec                ( ParseErrorBundle
                                                , errorBundlePretty
                                                )

data TestResult a
   = ParseRes a
   | ParseErr (ParseErrorBundle String Void)
   | ParseErrLiteral String

instance IsString (TestResult a) where
  fromString = ParseErrLiteral

instance (Eq a) => Eq (TestResult a) where
  (ParseRes        x) == (ParseRes        y ) = x == y
  (ParseErr        e) == (ParseErr        e') = e == e'
  (ParseErrLiteral s) == (ParseErrLiteral s') = s == s'
  (ParseErr        e) == (ParseErrLiteral s ) = errorBundlePretty e == s
  (ParseErrLiteral s) == (ParseErr        e ) = s == errorBundlePretty e
  _                   == _                    = False

instance (Show a) => Show (TestResult a) where
  show (ParseRes        x) = show x
  show (ParseErr        e) = errorBundlePretty e
  show (ParseErrLiteral s) = s

data TestCase a = TestCase
  { desc   :: String
  , inputs :: [String]
  , res    :: TestResult a
  }

spec :: Spec
spec = do
  describe "Statement" $ mapM_ (run evalParser) stmtCases
  describe "File" $ mapM_ (run $ fileParser "<test>") fileCases
 where
  run p tc = it (desc tc) $ mapM_ (flip (checkOne p) $ res tc) $ inputs tc
  checkOne p = shouldBe . either ParseErr ParseRes . p

fg :: String -> ITerm
fg = Free . Global

ifg :: String -> CTerm
ifg = Inf . fg

ib :: Int -> CTerm
ib = Inf . Bound

stmtCases :: [TestCase Stmt]
stmtCases =
  [ TestCase "Left associative function application"
             ["f x y", "(f x) y", "((f x) (y))"]
             (ParseRes . Eval Many $ fg "f" :$: ifg "x" :$: ifg "y")
  , TestCase "Annotated function application"
             ["f x : a", "(f x) : a", "(f x : (a))"]
             (ParseRes . Eval Many $ Ann (Inf $ fg "f" :$: ifg "x") (ifg "a"))
  , TestCase
    "Identity function"
    [ "\\a x . x : (0 a : U) -> (1 _ : a) -> a"
    , "λa x . x : ∀ (0 a : 𝘜) (1 _ : a) . a"
    , "w \\a x . x : (0 a : U) -> (1 _ : a) -> a"
    , "ω λa x . x : (0 a : U) → (1 _ : a) → a"
    , "ω λa x . x : ∀ (0 a : 𝘜) (1 _ : a) . a"
    ]
    (ParseRes . Eval Many $ Ann (Lam (Lam (ib 0)))
                                (Pi Zero Universe (Pi One (ib 0) (ib 1)))
    )
  , TestCase
    "Assumption"
    [ "assume (0 a : U) (1 x : a) (many : U)"
    , "assume(0a:U)(1x:a)(many:U)"
    , "assume (0 a : 𝘜) (1 x : a) (ω many : 𝘜)"
    , "assume(0a:𝘜)(1x:a)(ω many:𝘜)"
    , "assume(0a:𝘜)(1x:a)(w many:𝘜)"
    ]
    (ParseRes $ Assume
      [ Binding "a"    Zero Universe
      , Binding "x"    One  (ifg "a")
      , Binding "many" Many Universe
      ]
    )
  , TestCase
    "Multiplicative pair elimination"
    [ "let p @ x', y' = (x, f y z) : (0 x : a) * x in y'\n\
      \               : ((λu . a) : (0 _ : (0 z : U) * z) -> U) p"
    ]
    (ParseRes . Eval Many $ MPairElim
      (Ann (MPair (ifg "x") (Inf $ fg "f" :$: ifg "y" :$: ifg "z"))
           (MPairType Zero (ifg "a") (ib 0))
      )
      (ib 0)
      (Inf
        (Ann (Lam (ifg "a")) (Pi Zero (MPairType Zero Universe (ib 0)) Universe)
        :$: ib 0
        )
      )
    )
  , TestCase
    "Multiplicative unit elimination"
    ["0 let u @ () = f x in y : g u"]
    (ParseRes . Eval Zero $ MUnitElim (fg "f" :$: ifg "x")
                                      (ifg "y")
                                      (Inf $ fg "g" :$: ib 0)
    )
  , TestCase
    "Additive pair"
    ["let p = <x, f y> : (x : a) & f x", "let ω p = ⟨x, f y⟩ : (x : a) & f x"]
    (ParseRes . Let Many "p" $ Ann
      (APair (ifg "x") (Inf $ fg "f" :$: ifg "y"))
      (APairType (ifg "a") (Inf $ fg "f" :$: ib 0))
    )
  , TestCase
    "Additive pair elimination"
    ["1 λp. (fst p, snd p) : ∀ (p : (_ : a) & b) . (_ : a) * b"]
    (ParseRes . Eval One $ Ann
      (Lam (MPair (Inf (Fst (Bound 0))) (Inf (Snd (Bound 0)))))
      (Pi Many
          (APairType (ifg "a") (ifg "b"))
          (MPairType Many (ifg "a") (ifg "b"))
      )
    )
  , TestCase
    "Units"
    [ "(\\m a. m : forall (1 _ : I) (0 _ : T) . I) () <>"
    , "(λm a. m : ∀ (1 _ : 𝟭ₘ) (0 _ : ⊤) . 𝟭ₘ) () ⟨⟩"
    ]
    (   ParseRes
    .   Eval Many
    $   (Ann (Lam (Lam (ib 1))) (Pi One MUnitType (Pi Zero AUnitType MUnitType))
        :$: MUnit
        )
    :$: AUnit
    )
  , TestCase
    "Plentiful parentheses"
    [ "1 ((\\x y. ((x) : I))\n\
    \  : forall (1 _ : ((I)))\n\
    \    (_ : ((_ : (I)) * T))\n\
    \  . (I)) ((())) (((), <>))"
    ]
    (   ParseRes
    .   Eval One
    $   (   Ann
            (Lam (Lam (Inf (Ann (ib 1) MUnitType))))
            (Pi One
                MUnitType
                (Pi Many (MPairType Many MUnitType AUnitType) MUnitType)
            )
        :$: MUnit
        )
    :$: MPair MUnit AUnit
    )
  , TestCase
    "Missing parenthesis"
    ["f : (1 _ : a) -> U x"]
    "<interactive>:1:20:\n\
    \  |\n\
    \1 | f : (1 _ : a) -> U x\n\
    \  |                    ^\n\
    \unexpected 'x'\n\
    \expecting end of input\n"
  , TestCase
    "Pi type"
    [ "0 (x : a) -> b : U"
    , "0 (forall (x : a) . b) : U"
    , "0 ((w x : a) → b : U)"
    , "0 (ω x : a) → b : 𝘜"
    , "0 (∀ (ω x : a) . b) : 𝘜"
    ]
    (ParseRes . Eval Zero $ Ann (Pi Many (ifg "a") (ifg "b")) Universe)
  , TestCase
    "Multiplicative pair type"
    ["0 (w x : a) * b : U", "0 (x : (a)) * b : U", "0 (ω x : a) ⊗ b : 𝘜"]
    (ParseRes . Eval Zero $ Ann (MPairType Many (ifg "a") (ifg "b")) Universe)
  , TestCase
    "Additive pair type"
    ["0 (x : a) & b : U", "0 ((x : a) & b) : (U)", "0 (x : a) & b : 𝘜"]
    (ParseRes . Eval Zero $ Ann (APairType (ifg "a") (ifg "b")) Universe)
  ]

fileCases :: [TestCase [Stmt]]
fileCases =
  [ TestCase
      "Two lets"
      [ "let 1 v = let _ @ x,y = p in x : a\n\
        \\n\
        \let u = let _ @ () = () : I in x : a"
      ]
      (ParseRes
        [ Let One "v" $ MPairElim (fg "p") (ib 1) (ifg "a")
        , Let Many "u" $ MUnitElim (Ann MUnit MUnitType) (ifg "x") (ifg "a")
        ]
      )
  ]

