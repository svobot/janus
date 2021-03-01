{-# LANGUAGE LambdaCase #-}

module IntegrationSpec
  ( spec
  ) where

import           Control.Monad.State            ( foldM )
import           Data.Bifunctor                 ( bimap
                                                , first
                                                , second
                                                )
import           Data.String                    ( IsString
                                                , fromString
                                                )
import qualified Parser                        as Parse
import           Printer
import           Rig
import           Test.Hspec              hiding ( context )
import           Text.Parsec
import           Types
import           Typing

data TestCase = TestCase
  { desc  :: String
  , setup :: [String]
  , expr  :: String
  , res   :: TestResult
  }

data SetupError = PE ParseError | TE TypeError

newtype TestState = TestState { unState :: Either SetupError IState }

data TestResult = Literal String | TR (Result String)

instance IsString TestResult where
  fromString = Literal

instance Eq TestResult where
  x == y = show x == show y

instance Show TestResult where
  show (Literal s         ) = s
  show (TR      (Left  te)) = show te
  show (TR      (Right ty)) = ty

cases :: [TestCase]
cases =
  [ TestCase "Identity application"
             ["assume (0 a : U) (1 x : a)"]
             "1 (\\x. \\y. y : (0 x : U) -> (1 y : x) -> x) a x"
             "1 x : a"
  , TestCase "Let identity application"
             ["assume (0 a : U) (1 x : a)"]
             "let 1 id = (\\x. \\y. y : (0 x : U) -> (1 y : x) -> x) a x"
             "id = 1 x : a"
  , TestCase "Unknown variable in setup"
             ["assume (0 a : U) (1 x : b)"]
             ""
             "error: Variable not in scope: b"
  , TestCase
    "Erased linear variables in additive pair"
    ["assume (0 a : U) (0 b : U) (1 x : a) (1 y : b)"]
    "let 0 add = <x, y> : (x : a) & b"
    "error: Mismatched multiplicities:\n\
    \         x : a\n\
    \           Used 0-times, but available 1-times.\n\
    \         y : b\n\
    \           Used 0-times, but available 1-times."
  , TestCase
    "First projection of multiplicative pair under erasure"
    [ "assume (0 a : U) (0 b : U) (1 x : a) (1 y : b)"
    , "let 0 proj1 = λa b p. let z @ x, y = p in x : a\n\
      \            : ∀ (0 a : U)\n\
      \                (0 b : ∀ (0 a' : a) . U)\n\
      \                (0 p : (0 x : a) * b x)\n\
      \              . a"
    ]
    "0 proj1 a (\\x. b) (x, y)"
    "0 x : a"
  , TestCase
    "Second projection of multiplicative pair under erasure"
    [ "assume (0 a : U) (0 b : U) (1 x : a) (1 y : b)"
    , "let 0 proj1 = λa b p. let z @ x, y = p in x : a\n\
      \            : ∀ (0 a : U)\n\
      \                (0 b : ∀ (0 a' : a) . U)\n\
      \                (0 p : (0 x : a) * b x)\n\
      \              . a"
    , "let 0 proj2 = λa b p. let z @ x,y = p in y : b (proj1 a b z)\n\
      \            : ∀ (0 a : U)\n\
      \                (0 b : (0 a' : a) -> U)\n\
      \                (0 p : (0 x : a) * b x)\n\
      \              . b (proj1 a b p)"
    ]
    "0 proj2 a (\\x. b) (x, y)"
    "0 y : b"
  , TestCase
    "Multiplicative unit elimination"
    ["assume (0 a : U) (0 b : U) (1 x : a) (1 y : b)"]
    "1 (λp. let _ @ x, y = p in let _ @ () = y in x : a : a\n\
    \     : (1 _ : (1 _ : a) * I) -> a)\n\
    \   (x, ())"
    "1 x : a"
  , TestCase
    "Duplication of linear argument"
    []
    "(λx. (x, x) : ∀ (1 _ : I). (1 _ : I) * I) ()"
    "error: Mismatched multiplicities (lam):\n\
    \         [Local 0] : I\n\
    \           Used w-times, but available 1-times."
  , TestCase "Erased multiplicative usage of linear argument"
             []
             "(λx. (x, x) : ∀ (1 _ : I). (0 _ : I) * I) ()"
             "w ((), ()) : (0 x : I) * I"
  , TestCase "Additive usage of linear argument"
             []
             "(λx. <x, x> : ∀ (1 _ : I). (_ : I) & I) ()"
             "w <(), ()> : (x : I) & I"
  , TestCase
    "Exponential elimination"
    [ "assume (0 a : U) (m : a)"
    , "let 0 ofcW = (λa. (w _ : a) * I) : (0 _ : U) -> U"
    , "let w ofcElim = λa b exp f. let z @ x,y = exp in\n\
      \                              (let _ @ () = y in f x : b exp)\n\
      \                            : b exp\n\
      \              : ∀ (0 a : U)\n\
      \                  (0 b : (0 _ : (w _ : a) * I) -> U)\n\
      \                  (1 exp : ofcW a)\n\
      \                  (w f : (w x : a) -> b exp)\n\
      \                . b exp"
    ]
    "ofcElim a (λexp. (w _ : a) * a) (m, ()) (λmm. (mm, mm))"
    "w (m, m) : (w x : a) * a"
  ]

prettyCases :: [TestCase]
prettyCases =
  [ TestCase
    "Multiplicative pair first element projection"
    []
    "let 0 proj1 = λa b p. let z @ x, y = p in x : a\n\
    \            : ∀ (0 a : U)\n\
    \                (0 b : ∀ (0 a' : a) . U)\n\
    \                (0 p : (0 x : a) * b x)\n\
    \              . a"
    "proj1 = 0 λx y z. let c @ a, b = z in a : x\n\
    \        : ∀ (0 x : U) (0 y : (0 a : x) -> U) (0 z : (0 a : x) * y a) . x"
  , TestCase
    "Multiplicative pair second element projection"
    [ "let 0 proj1 = λa b p. let z @ x, y = p in x : a\n\
      \            : ∀ (0 a : U)\n\
      \                (0 b : ∀ (0 a' : a) . U)\n\
      \                (0 p : (0 x : a) * b x)\n\
      \              . a"
    ]
    "let 0 proj2 = λa b p. let z @ x,y = p in y : b (proj1 a b z)\n\
    \            : ∀ (0 a : U)\n\
    \                (0 b : (0 a' : a) -> U)\n\
    \                (0 p : (0 x : a) * b x)\n\
    \              . b (proj1 a b p)"
    "proj2 = 0 λx y z. let c @ a, b = z in b : y (let f @ d, e = c in d : x)\n\
    \        : ∀ (0 x : U) (0 y : (0 a : x) -> U) (0 z : (0 a : x) * y a) .\n\
    \          y (let c @ a, b = z in a : x)"
  , TestCase "SKI Calculus (I combinator)"
             []
             "let w Id = λ_ x. x : ∀ (0 a : U) (1 _ : a) . a"
             "Id = w λx y. y : ∀ (0 x : U) (1 y : x) . x"
  , TestCase
    "SKI Calculus (K combinator)"
    []
    "let w K = (λ_ _ x _. x)\n\
    \        : ∀ (0 a : U)\n\
    \            (0 b : (0 _ : a) -> U)\n\
    \            (1 x : a)\n\
    \            (w _ : b x)\n\
    \          . a"
    "K = w λx y z a. z : ∀ (0 x : U) (0 y : (0 b : x) -> U) (1 z : x) (w a : y z) . x"
  , TestCase
    "SKI Calculus (S combinator)"
    []
    "let w S = ((λa b c x y z. x z (y z))\n\
    \        : ∀ (0 a : U)\n\
    \            (0 b : (0 _ : a) -> U)\n\
    \            (0 c : ∀ (0 z : a) (0 yz : b z) . U)\n\
    \            (1 x : ∀ (w z : a) (1 yz : b z) . c z yz)\n\
    \            (1 y : (w z : a) -> b z)\n\
    \            (w z : a)\n\
    \          . c z (y z))"
    "S = w λx y z a b c. a c (b c)\n\
    \    : ∀ (0 x : U)\n\
    \        (0 y : (0 d : x) -> U)\n\
    \        (0 z : ∀ (0 d : x) (0 e : y d) . U)\n\
    \        (1 a : ∀ (w d : x) (1 e : y d) . z d e)\n\
    \        (1 b : (w d : x) -> y d)\n\
    \        (w c : x) .\n\
    \      z c (b c)"
  ]

withCases :: [TestCase]
withCases =
  [ TestCase
    "w <x, y> -> 1 (1 x, y)"
    ["assume (0 a : U) (0 b : U) (1 x : a) (1 y : b)"]
    "1 (λi. (fst i, snd i) : (w _ : (_ : a) & b) -> (1 _ : a) * b) <x, y>"
    "error: Mismatched multiplicities:\n\
    \         x : a\n\
    \           Used w-times, but available 1-times.\n\
    \         y : b\n\
    \           Used w-times, but available 1-times."
  , TestCase
    "w <x, y> -> 1 (1 x, x)"
    ["assume (0 a : U) (0 b : U) (1 x : a) (1 y : b)"]
    "1 (λi. (fst i, fst i) : (w _ : (_ : a) & b) -> (1 _ : a) * a) <x, y>"
    "error: Mismatched multiplicities:\n\
    \         x : a\n\
    \           Used w-times, but available 1-times.\n\
    \         y : b\n\
    \           Used w-times, but available 1-times."
  , TestCase
    "1 <x, y> -> 1 (1 x, y)"
    ["assume (0 a : U) (0 b : U) (1 x : a) (1 y : b)"]
    "1 (λi. (fst i, snd i) : (1 _ : (_ : a) & b) -> (1 _ : a) * b) <x, y>"
    "error: Mismatched multiplicities (lam):\n\
    \         [Local 0] : (x : a) & b\n\
    \           Used w-times, but available 1-times."
  , TestCase
    "1 <x, y> -> 1 (1 x, x)"
    ["assume (0 a : U) (0 b : U) (1 x : a) (1 y : b)"]
    "1 (λi. (fst i, fst i) : (1 _ : (_ : a) & b) -> (1 _ : a) * a) <x, y>"
    "error: Mismatched multiplicities (lam):\n\
    \         [Local 0] : (x : a) & b\n\
    \           Used w-times, but available 1-times."
  , TestCase
    "1 <m, y> -> 1 (w n, m)"
    ["assume (0 a : U) (0 b : U) (1 y : b) (m : a) (n : b)"]
    "1 (λi. (n, fst i) : (1 _ : (_ : a) & b) -> (_ : b) * a) <m, y>"
    "error: Mismatched multiplicities:\n\
    \         y : b\n\
    \           Used w-times, but available 1-times."
  , TestCase
    "1 <m, y> -> w (w n, m)"
    ["assume (0 a : U) (0 b : U) (1 y : b) (m : a) (n : b)"]
    "w (λi. (n, fst i) : (1 _ : (_ : a) & b) -> (_ : b) * a) <m, y>"
    "error: Mismatched multiplicities:\n\
    \         y : b\n\
    \           Used w-times, but available 1-times."
  ]

setContext :: [String] -> IO TestState
setContext s = return . TestState $ do
  stmts <- first PE (parseSetup s)
  foldM
    (\st stmt -> case stmt of
      (Parse.Assume bs) -> foldM
        (\st' (Binding x q t) -> do
          _ <- first TE $ iType0 (context st') Zero (Ann t Universe)
          let val = iEval (Ann t Universe) (fst $ context st, [])
          return $ st'
            { context = second (Binding (Global x) q val :) $ context st'
            }
        )
        st
        bs
      (Parse.Let q n i) -> do
        ty <- first TE $ iType0 (context st) q i
        let val = iEval i (fst $ context st, [])
        return $ st
          { context = bimap ((Global n, val) :) (Binding (Global n) q ty :)
                        $ context st
          }
      _ -> undefined
    )
    (IState "" ([], []))
    stmts
 where
  parseSetup :: [String] -> Either ParseError [Parse.Stmt]
  parseSetup = traverse (parse Parse.stmt "<setup>")

run :: TestCase -> Spec
run c = before (setContext $ setup c) (runTestCase c)
 where
  runTestCase :: TestCase -> SpecWith TestState
  runTestCase tc = it (desc tc) . flip (.) unState $ \case
    (Left  (PE e)) -> expectationFailure $ show e
    (Left  (TE e)) -> TR (Left e) `shouldBe` res tc
    (Right st    ) -> case parse Parse.stmt "<test>" (expr tc) of
      Left e -> expectationFailure $ show e
      Right (Parse.Eval q i) ->
        checkEval (context st) Nothing q i `shouldBe` res tc
      Right (Parse.Let q n i) ->
        checkEval (context st) (Just n) q i `shouldBe` res tc
      _ -> undefined

  checkEval ctx n q i =
    TR
      $   renderBindingPlain n
      .   Binding (iEval i (fst ctx, [])) q
      <$> iType0 ctx q i

spec :: Spec
spec = do
  mapM_ run cases
  describe "With-focused test cases" $ mapM_ run withCases
  describe "Pretty printer test cases" $ mapM_ run prettyCases

