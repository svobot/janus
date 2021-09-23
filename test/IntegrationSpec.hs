{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module IntegrationSpec
  ( spec
  ) where

import           Control.Monad.Reader           ( MonadReader(ask, local)
                                                , runReaderT
                                                )
import           Control.Monad.State            ( MonadState(..)
                                                , MonadTrans
                                                , StateT
                                                , evalStateT
                                                , execStateT
                                                , gets
                                                , lift
                                                , mapStateT
                                                , modify
                                                )
import           Data.Bifunctor                 ( second )
import           Data.String                    ( IsString
                                                , fromString
                                                )
import           Janus.Pretty
import           Janus.REPL
import           Janus.Style
import           Test.Hspec                     ( Spec
                                                , describe
                                                , it
                                                , shouldBe
                                                )

newtype TestIO m a = TestIO { runIO :: StateT ([String], [String]) m a}
  deriving (Monad, Functor, Applicative, MonadTrans)

instance MonadReader a m => MonadReader a (TestIO m) where
  ask = lift ask
  local f = TestIO . mapStateT (local f) . runIO

instance MonadState a m => MonadState a (TestIO m) where
  get = lift get
  put = lift . put

instance (Monad m) => MonadAbstractIO (TestIO m) where
  output s = TestIO $ modify (second (s :))
  outputDoc = output . renderString

-- New type is used to coerce hspec into printing failing test results across
-- multiple lines.
newtype TestResult = TestResult String

instance IsString TestResult where
  fromString = TestResult

instance Show TestResult where
  show (TestResult s) = s

instance Eq TestResult where
  x == y = show x == show y

data TestCase = TestCase
  { desc   :: String
  , input  :: [String]
  , result :: TestResult
  }

spec :: Spec
spec = do
  mapM_ runUnicode cases
  describe "Additive pair type test cases" $ mapM_ runUnicode withCases
  describe "Pretty printer test cases" $ mapM_ runUnicode prettyCases
  describe "Exponential type test cases" $ mapM_ runUnicode ofCourseCases
  describe "Test cases without unicode" $ mapM_ runAscii asciiCases
 where
  evalTestCase s i =
    flip evalStateT ([], []) . flip runReaderT s . flip execStateT (i, []) $ do
      st <- gets fst
      mapM_ (runIO . compileStmt) st

  run s c = it (desc c) $ do
    (_, out) <- evalTestCase s $ input c
    TestResult (head out) `shouldBe` result c

  runUnicode = run unicode
  runAscii   = run ascii

cases :: [TestCase]
cases =
  [ TestCase
    "Identity application"
    [ "assume (0 a : U) (1 x : a)"
    , "let 1 id = (\\x. \\y. y : (0 x : 𝘜) -> (1 y : x) -> x) a x"
    ]
    "1 id = x : a"
  , TestCase "Unknown variable"
             ["assume (0 a : U) (1 x : b)"]
             "error: Variable not in scope: b"
  , TestCase
    "Erased linear variables in additive pair"
    [ "assume (0 a : U) (0 b : U) (1 x : a) (1 y : b)"
    , "let 0 add = <x, y> : (x : a) & b"
    ]
    "error: Mismatched multiplicities:\n\
    \         x : a\n\
    \           Used 0-times, but available 1-times.\n\
    \         y : b\n\
    \           Used 0-times, but available 1-times."
  , TestCase
    "Projection to a first element of a multiplicative pair"
    [ "assume (0 a : U) (0 b : U) (w x : a) (w y : b)"
    , "let w proj1 = λa b p. let z @ (x, y) = p in x : a\n\
      \            : ∀ (0 a : U)\n\
      \                (0 b : ∀ (0 a' : a) . U)\n\
      \                (w p : (w x : a) * b x)\n\
      \              . a"
    , "w proj1 a (\\x. b) (x, y)"
    ]
    "ω x : a"
  , TestCase
    "Projection to a second element of a multiplicative pair"
    [ "assume (0 a : U) (0 b : U) (w x : a) (w y : b)"
    , "let w proj1 = λa b p. let z @ (x, y) = p in x : a\n\
      \            : ∀ (0 a : U)\n\
      \                (0 b : ∀ (0 a' : a) . U)\n\
      \                (w p : (w x : a) * b x)\n\
      \              . a"
    , "let w proj2 = λa b p. let z @ (x, y) = p in y : b (proj1 a b z)\n\
      \            : ∀ (0 a : U)\n\
      \                (0 b : (0 a' : a) -> U)\n\
      \                (w p : (w x : a) * b x)\n\
      \              . b (proj1 a b p)"
    , "w proj2 a (\\x. b) (x, y)"
    ]
    "ω y : b"
  , TestCase
    "Multiplicative unit elimination"
    [ "assume (0 a : U) (0 b : U) (1 x : a) (1 y : b)"
    , "1 (λp. let 1 _ @ (x, y) = p in let 1 _ @ () = y in x : a : a\n\
      \     : (1 _ : (1 _ : a) * I) -> a)\n\
      \   (x, ())"
    ]
    "1 x : a"
  , TestCase
    "Duplication of linear argument"
    ["(λx. (x, x) : ∀ (1 _ : I). (1 _ : I) * I) ()"]
    "error: Mismatched multiplicities (Lambda abstraction):\n\
    \         x : 𝟭ₘ\n\
    \           Used ω-times, but available 1-times."
  , TestCase "Erased multiplicative usage of linear argument"
             ["(λx. (x, x) : ∀ (1 _ : I). (0 _ : I) * I) ()"]
             "ω ((), ()) : (0 _ : 𝟭ₘ) ⊗ 𝟭ₘ"
  , TestCase "Additive usage of linear argument"
             ["(λx. <x, x> : ∀ (1 _ : I). (_ : I) & I) ()"]
             "ω ⟨(), ()⟩ : (_ : 𝟭ₘ) & 𝟭ₘ"
  , TestCase
    "Exponential elimination"
    [ "assume (0 a : U) (m : a)"
    , "let 0 ofcW = (λa. (w _ : a) * I) : (0 _ : U) -> U"
    , "let w ofcElim = λa b exp f. let 1 z @ (x, y) = exp in\n\
      \                              (let 1 _ @ () = y in f x : b exp)\n\
      \                            : b exp\n\
      \              : ∀ (0 a : U)\n\
      \                  (0 b : (0 _ : (w _ : a) * I) -> U)\n\
      \                  (1 exp : ofcW a)\n\
      \                  (w f : (w x : a) -> b exp)\n\
      \                . b exp"
    , "ofcElim a (λexp. (w _ : a) * a) (m, ()) (λm'. (m', m'))"
    ]
    "ω (m, m) : (ω _ : a) ⊗ a"
  , TestCase
    ""
    [ "assume (0 a : U) (m : a)"
    , "0 (λi. fst i : (i : (j : U) & j) -> U) <a, m>"
    ]
    "0 a : 𝘜"
  , TestCase "Type erasure"
             ["let 1 pair = (x : U) & U : U"]
             "error: Type '(x : 𝘜) & 𝘜' used 1-times outside erased context."
  , TestCase
    "Dependent additive pair elimination"
    ["assume (0 a : U) (0 s : a)", "let 0 res = snd (<a,s> : (a : U) & a)"]
    "0 res = s : a"
  , TestCase
    "Weakened disjoint sum usage in elimination branches"
    [ "assume (0 a : U) (0 b : U) (x : a) (y : b)"
    , "let 0 sum = a + b : U"
    , "let x' = case z @ inl x : sum of { inl x -> x; inr y -> x} : a"
    ]
    "ω x' = x : a"
  , TestCase
    "Linear disjoint sum usage in elimination branches"
    [ "assume (0 a : U) (0 b : U) (x : a) (y : b)"
    , "let 0 sum = a + b : U"
    , "let x' = case 1 z @ inl x : sum of { inl x -> x; inr y -> x} : a"
    ]
    "error: Mismatched multiplicities (Right case of the sum):\n\
    \         y : b\n\
    \           Used 0-times, but available 1-times."
  ]

prettyCases :: [TestCase]
prettyCases =
  [ TestCase "I combinator"
             ["let w Id = λ_ x. x : ∀ (0 a : U) (1 _ : a) . a"]
             "ω Id = (λ_ x. x) : ∀ (0 a : 𝘜) (1 _ : a) . a"
  , TestCase
    "K combinator"
    [ "let w K = (λ_ _ x _. x)\n\
      \        : ∀ (0 a : U)\n\
      \            (0 b : (0 _ : a) -> U)\n\
      \            (1 x : a)\n\
      \            (w _ : b x)\n\
      \          . a"
    ]
    "ω K = (λ_ _ x _. x)\n\
    \      : ∀ (0 a : 𝘜) (0 b : (0 _ : a) → 𝘜) (1 x : a) (ω _ : b x) . a"
  , TestCase
    "S combinator"
    [ "let w S = ((λa b c x y z. x z (y z))\n\
      \        : ∀ (0 a : U)\n\
      \            (0 b : (0 _ : a) -> U)\n\
      \            (0 c : ∀ (0 z : a) (0 yz : b z) . U)\n\
      \            (1 x : ∀ (w z : a) (1 yz : b z) . c z yz)\n\
      \            (1 y : (w z : a) -> b z)\n\
      \            (w z : a)\n\
      \          . c z (y z))"
    ]
    "ω S = (λa b c x y z. x z (y z))\n\
    \      : ∀ (0 a : 𝘜)\n\
    \          (0 b : (0 _ : a) → 𝘜)\n\
    \          (0 c : ∀ (0 z : a) (0 yz : b z) . 𝘜)\n\
    \          (1 x : ∀ (ω z : a) (1 yz : b z) . c z yz)\n\
    \          (1 y : (ω z : a) → b z)\n\
    \          (ω z : a)\n\
    \        . c z (y z)"
  ]

withCases :: [TestCase]
withCases =
  [ TestCase
    "w <x, y> -> 1 (1 x, y)"
    [ "assume (0 a : U) (0 b : U) (1 x : a) (1 y : b)"
    , "1 (λi. (fst i, snd i) : (w _ : (_ : a) & b) -> (1 _ : a) * b) <x, y>"
    ]
    "error: Mismatched multiplicities:\n\
    \         x : a\n\
    \           Used ω-times, but available 1-times.\n\
    \         y : b\n\
    \           Used ω-times, but available 1-times."
  , TestCase
    "w <x, y> -> 1 (1 x, x)"
    [ "assume (0 a : U) (0 b : U) (1 x : a) (1 y : b)"
    , "1 (λi. (fst i, fst i) : (w _ : (_ : a) & b) -> (1 _ : a) * a) <x, y>"
    ]
    "error: Mismatched multiplicities:\n\
    \         x : a\n\
    \           Used ω-times, but available 1-times.\n\
    \         y : b\n\
    \           Used ω-times, but available 1-times."
  , TestCase
    "1 <x, y> -> 1 (1 x, y)"
    [ "assume (0 a : U) (0 b : U) (1 x : a) (1 y : b)"
    , "1 (λi. (fst i, snd i) : (1 _ : (_ : a) & b) -> (1 _ : a) * b) <x, y>"
    ]
    "error: Mismatched multiplicities (Lambda abstraction):\n\
    \         i : (_ : a) & b\n\
    \           Used ω-times, but available 1-times."
  , TestCase
    "1 <x, y> -> 1 (1 x, x)"
    [ "assume (0 a : U) (0 b : U) (1 x : a) (1 y : b)"
    , "1 (λi. (fst i, fst i) : (1 _ : (_ : a) & b) -> (1 _ : a) * a) <x, y>"
    ]
    "error: Mismatched multiplicities (Lambda abstraction):\n\
    \         i : (_ : a) & b\n\
    \           Used ω-times, but available 1-times."
  , TestCase
    "1 <m, y> -> 1 (w n, m)"
    [ "assume (0 a : U) (0 b : U) (1 y : b) (m : a) (n : b)"
    , "1 (λi. (n, fst i) : (1 _ : (_ : a) & b) -> (_ : b) * a) <m, y>"
    ]
    "error: Mismatched multiplicities:\n\
    \         y : b\n\
    \           Used ω-times, but available 1-times."
  , TestCase
    "1 <m, y> -> w (w n, m)"
    [ "assume (0 a : U) (0 b : U) (1 y : b) (m : a) (n : b)"
    , "w (λi. (n, fst i) : (1 _ : (_ : a) & b) -> (_ : b) * a) <m, y>"
    ]
    "error: Mismatched multiplicities:\n\
    \         y : b\n\
    \           Used ω-times, but available 1-times."
  ]

ofCourseCases :: [TestCase]
ofCourseCases =
  [ TestCase
    "Exponential of a multiplicative pair produces a multiplicative pair of exponentials"
    [ ofcW
    , ofcElim
    , "(\\A B pair. ofcElim ((1 _ : A) * B)\n\
      \                     (\\_. (1 _ : ofcW A) * (ofcW B))\n\
      \                     pair\n\
      \                     (\\pair'. let w _ @ (x, y) = pair'\n\
      \                              in ((x, ()), (y, ()))\n\
      \                              : (1 _ : ofcW A) * (ofcW B)))\n\
      \: forall (0 A : U)\n\
      \         (0 B : U)\n\
      \         (1 _ : ofcW ((1 _ : A) * B))\n\
      \  . (1 _ : ofcW A) * (ofcW B)"
    ]
    "ω (λA B pair. let 1 exp' @ (val, unit) = pair\n\
    \              in let 1 unit' @ () = unit\n\
    \                 in let ω _ @ (x, y) = val\n\
    \                    in ((x, ()), (y, ()))\n\
    \                    : (1 _ : (ω _ : A) ⊗ 𝟭ₘ) ⊗ (ω _ : B) ⊗ 𝟭ₘ\n\
    \                 : (1 _ : (ω _ : A) ⊗ 𝟭ₘ) ⊗ (ω _ : B) ⊗ 𝟭ₘ\n\
    \              : (1 _ : (ω _ : A) ⊗ 𝟭ₘ) ⊗ (ω _ : B) ⊗ 𝟭ₘ)\n\
    \  : ∀ (0 A : 𝘜) (0 B : 𝘜) (1 _ : (ω _ : (1 _ : A) ⊗ B) ⊗ 𝟭ₘ)\n\
    \    . (1 _ : (ω _ : A) ⊗ 𝟭ₘ) ⊗ (ω _ : B) ⊗ 𝟭ₘ"
  , TestCase
    "Multiplicative pair of exponentials produces an exponential of a multiplicative pair"
    [ ofcW
    , ofcElim
    , "(\\A B pair. let 1 _ @ (x, y) = pair\n\
      \             in ofcElim A\n\
      \                        (\\_. ofcW ((1 _ : A) * B))\n\
      \                        x\n\
      \                        (\\x'. ofcElim B\n\
      \                                      (\\_. ofcW ((1 _ : A) * B))\n\
      \                                      y\n\
      \                                      (\\y'. ((x', y'), ())))\n\
      \             : ofcW ((1 _ : A) * B))\n\
      \: forall (0 A : U)\n\
      \         (0 B : U)\n\
      \         (1 _ : (1 _ : ofcW A) * (ofcW B))\n\
      \  . ofcW ((1 _ : A) * B)"
    ]
    "ω (λA B pair. let 1 _ @ (x, y) = pair\n\
    \              in let 1 exp' @ (val, unit) = x\n\
    \                 in let 1 unit' @ () = unit\n\
    \                    in let 1 exp' @ (val, unit) = y\n\
    \                       in let 1 unit' @ () = unit\n\
    \                          in ((val#1, val), ())\n\
    \                          : (ω _ : (1 _ : A) ⊗ B) ⊗ 𝟭ₘ\n\
    \                       : (ω _ : (1 _ : A) ⊗ B) ⊗ 𝟭ₘ\n\
    \                    : (ω _ : (1 _ : A) ⊗ B) ⊗ 𝟭ₘ\n\
    \                 : (ω _ : (1 _ : A) ⊗ B) ⊗ 𝟭ₘ\n\
    \              : (ω _ : (1 _ : A) ⊗ B) ⊗ 𝟭ₘ)\n\
    \  : ∀ (0 A : 𝘜) (0 B : 𝘜) (1 _ : (1 _ : (ω _ : A) ⊗ 𝟭ₘ) ⊗ (ω _ : B) ⊗ 𝟭ₘ)\n\
    \    . (ω _ : (1 _ : A) ⊗ B) ⊗ 𝟭ₘ"
  , TestCase
    "Exponential of an additive pair produces an additive pair of exponentials"
    [ ofcW
    , ofcElim
    , "(\\A B pair. ofcElim ((_ : A) & B)\n\
      \                     (\\_. (_ : ofcW A) & (ofcW B))\n\
      \                     pair\n\
      \                     (\\pair'. <(fst pair', ()), (snd pair', ())>))\n\
      \: forall (0 A : U)\n\
      \         (0 B : U)\n\
      \         (1 _ : ofcW ((_ : A) & B))\n\
      \  . (_ : ofcW A) & (ofcW B)"
    ]
    "ω (λA B pair. let 1 exp' @ (val, unit) = pair\n\
    \              in let 1 unit' @ () = unit\n\
    \                 in ⟨(fst val, ()), (snd val, ())⟩\n\
    \                 : (_ : (ω _ : A) ⊗ 𝟭ₘ) & (ω _ : B) ⊗ 𝟭ₘ\n\
    \              : (_ : (ω _ : A) ⊗ 𝟭ₘ) & (ω _ : B) ⊗ 𝟭ₘ)\n\
    \  : ∀ (0 A : 𝘜) (0 B : 𝘜) (1 _ : (ω _ : (_ : A) & B) ⊗ 𝟭ₘ)\n\
    \    . (_ : (ω _ : A) ⊗ 𝟭ₘ) & (ω _ : B) ⊗ 𝟭ₘ"
  , TestCase
    "Additive pair of exponentials fails to produce an exponential of an additive pair"
    [ ofcW
    , ofcElim
    , "(\\A B pair. ofcElim A\n\
      \                     (\\_. ofcW ((_ : A) & B))\n\
      \                     (fst pair)\n\
      \                     (\\x. ofcElim B\n\
      \                                  (\\_. ofcW ((_ : A) & B))\n\
      \                                  (snd pair)\n\
      \                                  (\\y. (<x, y>, ()))))\n\
      \: forall (0 A : U)\n\
      \         (0 B : U)\n\
      \         (1 _ : (_ : ofcW A) & (ofcW B))\n\
      \  . ofcW ((_ : A) & B)"
    ]
    "error: Mismatched multiplicities (Lambda abstraction):\n\
    \         pair : (_ : (ω _ : A) ⊗ 𝟭ₘ) & (ω _ : B) ⊗ 𝟭ₘ\n\
    \           Used ω-times, but available 1-times."
  , TestCase
    "Additive pair of exponentials fails to produce an exponential of an additive pair (different form)"
    [ ofcW
    , ofcElim
    , "(\\A B pair. (<ofcElim A (\\_. A) (fst pair) (\\x. x),\n\
      \               ofcElim B (\\_. B) (snd pair) (\\y. y)>, ()))\n\
      \: forall (0 A : U)\n\
      \         (0 B : U)\n\
      \         (1 _ : (_ : ofcW A) & (ofcW B))\n\
      \  . ofcW ((_ : A) & B)"
    ]
    "error: Mismatched multiplicities (Lambda abstraction):\n\
    \         pair : (_ : (ω _ : A) ⊗ 𝟭ₘ) & (ω _ : B) ⊗ 𝟭ₘ\n\
    \           Used ω-times, but available 1-times."
  , TestCase
    "Exponential of a disjoint sum produces a disjoint sum of exponentials"
    [ ofcW
    , ofcElim
    , "(\\A B sum. ofcElim (A + B)\n\
      \                    (\\_. (ofcW A) + (ofcW B))\n\
      \                    sum\n\
      \                    (\\sum'. case w _ @ sum'\n\
      \                            of { inl x -> inl (x, ());\n\
      \                                 inr y -> inr (y, ())\n\
      \                               } : (ofcW A) + (ofcW B)))\n\
      \: forall (0 A : U)\n\
      \         (0 B : U)\n\
      \         (1 _ : ofcW (A + B))\n\
      \  . (ofcW A) + (ofcW B)"
    ]
    "ω (λA B sum. let 1 exp' @ (val, unit) = sum\n\
    \             in let 1 unit' @ () = unit\n\
    \                in case ω _ @ val of { inl x → inl (x, ()); inr y → inr (y, ())\n\
    \                                     } : (ω _ : A) ⊗ 𝟭ₘ ⊕ (ω _ : B) ⊗ 𝟭ₘ\n\
    \                : (ω _ : A) ⊗ 𝟭ₘ ⊕ (ω _ : B) ⊗ 𝟭ₘ\n\
    \             : (ω _ : A) ⊗ 𝟭ₘ ⊕ (ω _ : B) ⊗ 𝟭ₘ)\n\
    \  : ∀ (0 A : 𝘜) (0 B : 𝘜) (1 _ : (ω _ : A ⊕ B) ⊗ 𝟭ₘ)\n\
    \    . (ω _ : A) ⊗ 𝟭ₘ ⊕ (ω _ : B) ⊗ 𝟭ₘ"
  , TestCase
    "Disjoint sum of exponentials produces an exponential of disjoint sums"
    [ ofcW
    , ofcElim
    , "(\\A B sum. case 1 _ @ sum of\n\
      \            { inl x -> ofcElim A (\\_. ofcW (A + B)) x (\\x'. (inl x', ()));\n\
      \              inr y -> ofcElim B (\\_. ofcW (A + B)) y (\\y'. (inr y', ()))\n\
      \            } : ofcW (A + B))\n\
      \: forall (0 A : U)\n\
      \         (0 B : U)\n\
      \         (1 _ : (ofcW A) + (ofcW B))\n\
      \  . ofcW (A + B)"
    ]
    "ω (λA B sum. case 1 _ @ sum of { inl x → let 1 exp' @ (val, unit) = x\n\
    \                                         in let 1 unit' @ () = unit\n\
    \                                            in (inl val, ())\n\
    \                                            : (ω _ : A ⊕ B) ⊗ 𝟭ₘ\n\
    \                                         : (ω _ : A ⊕ B) ⊗ 𝟭ₘ;\n\
    \                                 inr y → let 1 exp' @ (val, unit) = y\n\
    \                                         in let 1 unit' @ () = unit\n\
    \                                            in (inr val, ())\n\
    \                                            : (ω _ : A ⊕ B) ⊗ 𝟭ₘ\n\
    \                                         : (ω _ : A ⊕ B) ⊗ 𝟭ₘ\n\
    \                               } : (ω _ : A ⊕ B) ⊗ 𝟭ₘ)\n\
    \  : ∀ (0 A : 𝘜) (0 B : 𝘜) (1 _ : (ω _ : A) ⊗ 𝟭ₘ ⊕ (ω _ : B) ⊗ 𝟭ₘ)\n\
    \    . (ω _ : A ⊕ B) ⊗ 𝟭ₘ"
  , TestCase
    "Exponential of a dependent multiplicative pair produces a dependent multiplicative pair of exponentials"
    [ ofcW
    , ofcElim
    , unwrap
    , "(\\A B wab. ofcElim ((1 a : A) * B a)\n\
      \            (\\_. (1 wa : ofcW A) * ofcW (B (unwrap A wa)))\n\
      \            wab\n\
      \            (\\ab. let w _ @ (a, b) = ab\n\
      \                   in ((a, ()), (b, ()))\n\
      \                   : (1 wa : ofcW A) * ofcW (B (unwrap A wa))))\n\
      \: forall (0 A : U)\n\
      \         (0 B : (0 _ : A) -> U)\n\
      \         (1 _ : ofcW ((1 a : A) * B a))\n\
      \  . (1 wa : ofcW A) * ofcW (B (unwrap A wa))"
    ]
    "ω (λA B wab. let 1 exp' @ (val, unit) = wab\n\
    \             in let 1 unit' @ () = unit\n\
    \                in let ω _ @ (a, b) = val\n\
    \                   in ((a, ()), (b, ()))\n\
    \                   : (1 wa : (ω _ : A) ⊗ 𝟭ₘ) ⊗\n\
    \                     (ω _\n\
    \                      : B\n\
    \                        (let 1 exp' @ (val, unit) = wa\n\
    \                         in let 1 unit' @ () = unit in val : A\n\
    \                         : A)) ⊗\n\
    \                     𝟭ₘ\n\
    \                : (1 wa : (ω _ : A) ⊗ 𝟭ₘ) ⊗\n\
    \                  (ω _\n\
    \                   : B\n\
    \                     (let 1 exp' @ (val, unit) = wa\n\
    \                      in let 1 unit' @ () = unit in val : A\n\
    \                      : A)) ⊗\n\
    \                  𝟭ₘ\n\
    \             : (1 wa : (ω _ : A) ⊗ 𝟭ₘ) ⊗\n\
    \               (ω _\n\
    \                : B\n\
    \                  (let 1 exp' @ (val, unit) = wa\n\
    \                   in let 1 unit' @ () = unit in val : A\n\
    \                   : A)) ⊗\n\
    \               𝟭ₘ)\n\
    \  : ∀ (0 A : 𝘜) (0 B : (0 _ : A) → 𝘜) (1 _ : (ω _ : (1 a : A) ⊗ B a) ⊗ 𝟭ₘ)\n\
    \    . (1 wa : (ω _ : A) ⊗ 𝟭ₘ) ⊗\n\
    \      (ω _\n\
    \       : B\n\
    \         (let 1 exp' @ (val, unit) = wa\n\
    \          in let 1 unit' @ () = unit in val : A\n\
    \          : A)) ⊗\n\
    \      𝟭ₘ"
  , TestCase
    "Dependent multiplicative pair of exponentials produces an exponential of a dependent multiplicative pair"
    [ ofcW
    , ofcElim
    , unwrap
    , "(\\A B wawb. let 1 _ @ (wa, wb) = wawb\n\
      \             in ofcElim A\n\
      \                        (\\wa'. (1 _ : ofcW (B (unwrap A wa'))) -> ofcW ((1 a : A) * B a))\n\
      \                        wa\n\
      \                        (\\a wb'. ofcElim (B a)\n\
      \                                          (\\_. ofcW ((1 a : A) * B a))\n\
      \                                          wb'\n\
      \                                          (\\b. ((a, b), ()))\n\
      \                        )\n\
      \                wb\n\
      \             : ofcW ((1 a : A) * B a))\n\
      \: forall (0 A : U)\n\
      \         (0 B : (0 _ : A) -> U)\n\
      \         (1 _ : (1 wa : ofcW A) * ofcW (B (unwrap A wa)))\n\
      \  . ofcW ((1 a : A) * B a)"
    ]
    "ω (λA B wawb. let 1 _ @ (wa, wb) = wawb\n\
    \              in (let 1 exp' @ (val, unit) = wa\n\
    \                  in let 1 unit' @ () = unit\n\
    \                     in λwb'. let 1 exp' @ (val, unit) = wb'\n\
    \                              in let 1 unit' @ () = unit\n\
    \                                 in ((val#1, val), ())\n\
    \                                 : (ω _ : (1 a : A) ⊗ B a) ⊗ 𝟭ₘ\n\
    \                              : (ω _ : (1 a : A) ⊗ B a) ⊗ 𝟭ₘ\n\
    \                     : (1 _\n\
    \                        : (ω _ : B (let 1 unit' @ () = unit' in val : A)) ⊗\n\
    \                          𝟭ₘ) →\n\
    \                       (ω _ : (1 a : A) ⊗ B a) ⊗ 𝟭ₘ\n\
    \                  : (1 _\n\
    \                     : (ω _\n\
    \                        : B\n\
    \                          (let 1 exp' @ (val, unit) = exp'\n\
    \                           in let 1 unit' @ () = unit in val : A\n\
    \                           : A)) ⊗\n\
    \                       𝟭ₘ) →\n\
    \                    (ω _ : (1 a : A) ⊗ B a) ⊗ 𝟭ₘ)\n\
    \                 wb\n\
    \              : (ω _ : (1 a : A) ⊗ B a) ⊗ 𝟭ₘ)\n\
    \  : ∀ (0 A : 𝘜)\n\
    \      (0 B : (0 _ : A) → 𝘜)\n\
    \      (1 _ : (1 wa : (ω _ : A) ⊗ 𝟭ₘ) ⊗\n\
    \             (ω _\n\
    \              : B\n\
    \                (let 1 exp' @ (val, unit) = wa\n\
    \                 in let 1 unit' @ () = unit in val : A\n\
    \                 : A)) ⊗\n\
    \             𝟭ₘ)\n\
    \    . (ω _ : (1 a : A) ⊗ B a) ⊗ 𝟭ₘ"
  , TestCase
    "Exponential of a dependent additive pair produces a dependent additive pair of exponentials"
    [ ofcW
    , ofcElim
    , unwrap
    , "(\\A B wab. ofcElim ((a : A) & B a)\n\
      \                    (\\_. (wa : ofcW A) & (ofcW (B (unwrap A wa))))\n\
      \                    wab\n\
      \                    (\\ab. <(fst ab, ()), (snd ab, ())>))\n\
      \: forall (0 A : U)\n\
      \         (0 B : (0 _ : A) -> U)\n\
      \         (1 _ : ofcW ((a : A) & B a))\n\
      \  . (wa : ofcW A) & (ofcW (B (unwrap A wa)))"
    ]
    "ω (λA B wab. let 1 exp' @ (val, unit) = wab\n\
    \             in let 1 unit' @ () = unit\n\
    \                in ⟨(fst val, ()), (snd val, ())⟩\n\
    \                : (wa : (ω _ : A) ⊗ 𝟭ₘ) &\n\
    \                  (ω _\n\
    \                   : B\n\
    \                     (let 1 exp' @ (val, unit) = wa\n\
    \                      in let 1 unit' @ () = unit in val : A\n\
    \                      : A)) ⊗\n\
    \                  𝟭ₘ\n\
    \             : (wa : (ω _ : A) ⊗ 𝟭ₘ) &\n\
    \               (ω _\n\
    \                : B\n\
    \                  (let 1 exp' @ (val, unit) = wa\n\
    \                   in let 1 unit' @ () = unit in val : A\n\
    \                   : A)) ⊗\n\
    \               𝟭ₘ)\n\
    \  : ∀ (0 A : 𝘜) (0 B : (0 _ : A) → 𝘜) (1 _ : (ω _ : (a : A) & B a) ⊗ 𝟭ₘ)\n\
    \    . (wa : (ω _ : A) ⊗ 𝟭ₘ) &\n\
    \      (ω _\n\
    \       : B\n\
    \         (let 1 exp' @ (val, unit) = wa\n\
    \          in let 1 unit' @ () = unit in val : A\n\
    \          : A)) ⊗\n\
    \      𝟭ₘ"
  , TestCase
    "Dependent additive pair of exponentials fails to produce an exponential of a dependent additive pair"
    [ ofcW
    , ofcElim
    , unwrap
    , "(\\A B wawb. (<unwrap A (fst wawb)\n\
       \             , unwrap (B (unwrap A (fst wawb))) (snd wawb)>\n\
       \            , ()))\n\
       \: forall (0 A : U)\n\
       \         (0 B : (0 _ : A) -> U)\n\
       \         (1 _ : (wa : ofcW A) & (ofcW (B (unwrap A wa))))\n\
       \  . ofcW ((a : A) & B a)"
    ]
    "error: Mismatched multiplicities (Lambda abstraction):\n\
    \         wawb : (wa : (ω _ : A) ⊗ 𝟭ₘ) &\n\
    \                (ω _\n\
    \                 : B\n\
    \                   (let 1 exp' @ (val, unit) = wa\n\
    \                    in let 1 unit' @ () = unit in val : A\n\
    \                    : A)) ⊗\n\
    \                𝟭ₘ\n\
    \           Used ω-times, but available 1-times."
  ]
 where
  ofcW = "let 0 ofcW = (λA. (ω _ : A) ⊗ 𝟭ₘ) : (0 _ : 𝘜) → 𝘜"
  ofcElim
    = "let ω ofcElim = (λ_ B exp cont. let 1 exp' @ (val, unit) = exp\n\
      \                                in let 1 unit' @ () = unit\n\
      \                                   in cont val\n\
      \                                   : B (val, unit')\n\
      \                                : B exp')\n\
      \                : ∀ (0 A : 𝘜)\n\
      \                    (0 B : (0 _ : (ω _ : A) ⊗ 𝟭ₘ) → 𝘜)\n\
      \                    (1 exp : (ω _ : A) ⊗ 𝟭ₘ)\n\
      \                    (1 _ : (ω val : A) → B (val, ()))\n\
      \                  . B exp"
  unwrap
    = "let unwrap = (\\A wa. ofcElim A (\\_. A) wa (\\x. x))\n\
      \             : (0 A : U) -> (_ : ofcW A) -> A"

asciiCases :: [TestCase]
asciiCases =
  [ TestCase
    "K combinator"
    [ "let ω K = (λ_ _ x _. x)\n\
      \        : ∀ (0 a : U)\n\
      \            (0 b : (0 _ : a) -> U)\n\
      \            (1 x : a)\n\
      \            (ω _ : b x)\n\
      \          . a"
    ]
    "w K = (\\_ _ x _. x)\n\
      \      : forall (0 a : U) (0 b : (0 _ : a) -> U) (1 x : a) (w _ : b x) . a"
  , TestCase "Additive and multiplicative units"
             ["let 0 u = <<>, ()> : (_ : T) & I"]
             "0 u = <<>, ()> : (_ : T) & I"
  ]

