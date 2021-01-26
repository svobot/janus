module ParseSpec
  ( spec
  ) where

import           Parser
import           Rig
import           Test.Hspec
import           Text.Parsec                    ( parse )
import           Types

data SuccTest = SuccTest String String Stmt

succTests :: [SuccTest]
succTests =
  [ SuccTest "Left associative application"
             "f x y"
             (Eval $ fg "f" :$: ifg "x" :$: ifg "y")
  , SuccTest
    "Annotated identity function"
    "(\\ a x . x) : (0 a : U) -> (1 x : a) -> a"
    (Eval $ Ann (Lam (Lam (ib 0))) (Pi Zero Universe (Pi One (ib 0) (ib 1))))
  , SuccTest "Dependent assumption"
             "assume (0 a : U) (1 x : a)"
             (Assume [Binding "a" Zero Universe, Binding "x" One (ifg "a")])
  , SuccTest "Multiplicative pair eleminator"
             "let w @ x, y = z in y : a"
             (Eval $ PairElim (fg "z") (ib 0) (ifg "a"))
  , SuccTest
    "Annotated multiplicative pair elimination"
    "let w @ x', y' = (x,y) : (0 x : a) * x in y' : d"
    (Eval $ PairElim
      (Ann (Pair (ifg "x") (ifg "y")) (Tensor Zero (ifg "a") (ib 0)))
      (ib 0)
      (ifg "d")
    )
  , SuccTest
    "Complex multiplicative pair"
    "(x, f y z) : (0 x : a) * x"
    (Eval $ Ann (Pair (ifg "x") (Inf $ fg "f" :$: ifg "y" :$: ifg "z"))
                (Tensor Zero (ifg "a") (ib 0))
    )
  , SuccTest "Annotated multiplicative unit elimination"
             "let x @ () = () : MUnit in () : MUnit"
             (Eval $ MUnitElim (Ann MUnit MUnitType) MUnit MUnitType)
  , SuccTest "Annotated function application"
             "f x : a"
             (Eval $ Ann (Inf $ fg "f" :$: ifg "x") (ifg "a"))
  , SuccTest
    "Multiplicative pair 'fst' projection"
    "let 0 fst = (\\ a b p. let z @ x,y = p in x : a) : (0 a: U) -> (0 b : (0 a' : a) -> U) -> (0 p : (0 x : a) * b x) -> a"
    (Let Zero "fst" $ Ann
      (Lam (Lam (Lam (Inf (PairElim (Bound 0) (ib 1) (ib 3))))))
      (Pi
        Zero
        Universe
        (Pi Zero
            (Pi Zero (ib 0) Universe)
            (Pi Zero (Tensor Zero (ib 1) (Inf (Bound 1 :$: ib 0))) (ib 2))
        )
      )
    )
  , SuccTest
    "Additive pair"
    "let 1 x = <y, f z> : (x : U) & U"
    ( Let One "x"
    $ Ann
        (Angles (ifg "y") (Inf (fg "f" :$: ifg "z")))
        (With Universe Universe)
    )
  , SuccTest
    "Nested pairs"
    "(<>, ((U, U))) : (0 x : AUnit) * (0 y : U) * U"
    (Eval $ Ann (Pair AUnit (Pair Universe Universe))
                (Tensor Zero AUnitType (Tensor Zero Universe Universe))
    )
  ]
 where
  fg  = Free . Global
  ifg = Inf . fg
  ib  = Inf . Bound

succTestSpec :: SuccTest -> SpecWith ()
succTestSpec (SuccTest d i r) = it d $ parse (stmt []) i i `shouldBe` Right r

spec :: Spec
spec = mapM_ succTestSpec succTests

