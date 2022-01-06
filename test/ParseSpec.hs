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
  describe "Variable shadowing" $ mapM_ (run evalParser) shadowedCases
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
    (ParseRes . Eval Many $ Ann
      (Lam "a" (Lam "x" (ib 0)))
      (Pi Zero "a" Universe (Pi One "_" (ib 0) (ib 1)))
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
    [ "let p @ (x', y') = (x, f y z) : (0 x : a) * x in y'\n\
      \                 : ((λu . a) : (0 _ : (0 z : U) * z) -> U) p"
    , "let p@(x',y')=(x,f y z):(0x:a)*x in y'\n\
      \             :((λu.a):(0_:(0 z:U)*z)->U)p"
    ]
    (ParseRes . Eval Many $ MPairElim
      Many
      "p"
      "x'"
      "y'"
      (Ann (MPair (ifg "x") (Inf $ fg "f" :$: ifg "y" :$: ifg "z"))
           (MPairType Zero "x" (ifg "a") (ib 0))
      )
      (ib 0)
      (Inf
        (   Ann (Lam "u" (ifg "a"))
                (Pi Zero "_" (MPairType Zero "z" Universe (ib 0)) Universe)
        :$: ib 0
        )
      )
    )
  , TestCase
    "Multiplicative unit elimination"
    ["0 let u @ () = f x in y : g u", "0 let u@()=f x in y:g u"]
    (ParseRes . Eval Zero $ MUnitElim Many
                                      "u"
                                      (fg "f" :$: ifg "x")
                                      (ifg "y")
                                      (Inf $ fg "g" :$: ib 0)
    )
  , TestCase
    "Additive pair"
    ["let p = <x, f y> : (x : a) & f x", "let ω p = ⟨x, f y⟩ : (x : a) & f x"]
    (ParseRes . Let Many "p" $ Ann
      (APair (ifg "x") (Inf $ fg "f" :$: ifg "y"))
      (APairType "x" (ifg "a") (Inf $ fg "f" :$: ib 0))
    )
  , TestCase
    "Additive pair elimination"
    ["1 λp. (fst p, snd p) : ∀ (p : (_ : a) & b) . (_ : a) * b"]
    (ParseRes . Eval One $ Ann
      (Lam "p" (MPair (Inf (Fst (Bound 0))) (Inf (Snd (Bound 0)))))
      (Pi Many
          "p"
          (APairType "_" (ifg "a") (ifg "b"))
          (MPairType Many "_" (ifg "a") (ifg "b"))
      )
    )
  , TestCase
    "Units"
    [ "(\\m a. m : forall (1 _ : I) (0 _ : T) . I) () <>"
    , "(λm a. m : ∀ (1 _ : 𝟭ₘ) (0 _ : ⊤) . 𝟭ₘ) () ⟨⟩"
    ]
    (   ParseRes
    .   Eval Many
    $   Ann (Lam "m" (Lam "a" (ib 1)))
            (Pi One "_" MUnitType (Pi Zero "_" AUnitType MUnitType))
    :$: MUnit
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
            (Lam "x" (Lam "y" (Inf (Ann (ib 1) MUnitType))))
            (Pi
              One
              "_"
              MUnitType
              (Pi Many "_" (MPairType Many "_" MUnitType AUnitType) MUnitType)
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
    (ParseRes . Eval Zero $ Ann (Pi Many "x" (ifg "a") (ifg "b")) Universe)
  , TestCase
    "Multiplicative pair type"
    ["0 (w x : a) * b : U", "0 (x : (a)) * b : U", "0 (ω x : a) ⊗ b : 𝘜"]
    (ParseRes . Eval Zero $ Ann (MPairType Many "x" (ifg "a") (ifg "b"))
                                Universe
    )
  , TestCase
    "Additive pair type"
    ["0 (x : a) & b : U", "0 ((x : a) & b) : (U)", "0 (x : a) & b : 𝘜"]
    (ParseRes . Eval Zero $ Ann (APairType "x" (ifg "a") (ifg "b")) Universe)
  , TestCase
    "Disjoint sum"
    ["1 inr x : (f a) + b"]
    (ParseRes . Eval One $ Ann (SumR $ ifg "x")
                               (SumType (Inf $ fg "f" :$: ifg "a") (ifg "b"))
    )
  , TestCase
    "Disjoint sum elimination"
    [ "let sum = case z @ m of {inl x -> x; inr y -> f y} : a"
    , "let sum=case z@m of{inl x->x;inr y->f y}:a"
    , "let sum = case z @ m of {inr y -> f y; inl x -> x} : a"
    , "let sum = case w z @ m of {inl x -> x; inr y -> f y} : a"
    , "let ω sum = case ω z @ m of {inl x -> x; inr y -> f y} : a"
    ]
    (ParseRes . Let Many "sum" $ SumElim Many
                                         "z"
                                         (fg "m")
                                         "x"
                                         (ib 0)
                                         "y"
                                         (Inf $ fg "f" :$: ib 0)
                                         (ifg "a")
    )
  , TestCase
    "Composed type"
    [ "let 0 Bool = I + I : U"
    , "let 0 Bool = (I) + I : U"
    , "let 0 Bool = (((I) + (I)) : (U))"
    ]
    (ParseRes . Let Zero "Bool" $ Ann (SumType MUnitType MUnitType) Universe)
  , TestCase
    "Nested function application"
    ["f ((a b) c)"]
    (ParseRes . Eval Many $ Free (Global "f") :$: Inf
      (   (Free (Global "a") :$: Inf (Free (Global "b")))
      :$: Inf (Free (Global "c"))
      )
    )
  ]

shadowedCases :: [TestCase Stmt]
shadowedCases =
  [ TestCase
    "Binding De Bruijn index 0"
    [ "let 1 id = (\\x. \\x. x : (0 x : 𝘜) -> (1 y : U) -> U)"
    , "let 1 id = (\\x. \\x. x#0 : (0 x : 𝘜) -> (1 y : U) -> U)"
    ]
    (ParseRes . Let One "id" $ Ann
      (Lam "x" (Lam "x" (ib 0)))
      (Pi Zero "x" Universe (Pi One "y" Universe Universe))
    )
  , TestCase
    "Binding De Bruijn index 1"
    ["let 1 id = (\\x. \\x. x#1 : (1 x : 𝘜) -> (0 y : U) -> U)"]
    (ParseRes . Let One "id" $ Ann
      (Lam "x" (Lam "x" (ib 1)))
      (Pi One "x" Universe (Pi Zero "y" Universe Universe))
    )
  , TestCase
    "Binding too large index"
    ["let 1 id = (\\x. \\x. x#10 : (1 x : 𝘜) -> (0 y : U) -> U)"]
    "<interactive>:1:21:\n\
    \  |\n\
    \1 | let 1 id = (\\x. \\x. x#10 : (1 x : 𝘜) -> (0 y : U) -> U)\n\
    \  |                     ^\n\
    \index of the bound variable is too large\n\
    \only 2 variables 'x' are in context\n"
  ]

fileCases :: [TestCase [Stmt]]
fileCases =
  [ TestCase
      "Two lets"
      [ "let 1 v = let _ @ (x, y) = p in x : a\n\
        \\n\
        \let u = let _ @ () = () : I in x : a"
      ]
      (ParseRes
        [ Let One "v" $ MPairElim Many "_" "x" "y" (fg "p") (ib 1) (ifg "a")
        , Let Many "u"
          $ MUnitElim Many "_" (Ann MUnit MUnitType) (ifg "x") (ifg "a")
        ]
      )
  ]

