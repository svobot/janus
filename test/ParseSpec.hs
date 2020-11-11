module ParseSpec
  ( spec
  )
where

import           Control.Monad                  ( foldM )
import           Parser
import           Test.Hspec
import           Text.Parsec                    ( parse )
import           Types

data SuccTest = SuccTest String String Stmt

succTests :: [SuccTest]
succTests =
  [ SuccTest "Left associative application"
             "f x y"
             (Eval $ fg "f" :@: ifg "x" :@: ifg "y")
  , SuccTest
    "Annotated identity function"
    "(\\ a x . x) : (0 a : *) -> (1 x : a) -> a"
    (Eval $ Ann (Lam (Lam (ib 0))) (Pi Rig0 Star (Pi Rig1 (ib 0) (ib 1))))
  , SuccTest "Dependent assumption"
             "assume (0 a : *) (1 x : a)"
             (Assume [(Rig0, "a", Star), (Rig1, "x", ifg "a")])
  , SuccTest "Free pair eleminator"
             "let w @ x, y = z in y : a"
             (Eval $ PairElim (fg "z") (ib 0) (ifg "a"))
  , SuccTest
    "Annotated pair elimination"
    "let w @ x', y' = (x,y) : (0 x : a) * x in y' : d"
    (Eval $ PairElim
      (Ann (Pair (ifg "x") (ifg "y")) (TensPr Rig0 (ifg "a") (ib 0)))
      (ib 0)
      (ifg "d")
    )
  , SuccTest
    "Complex pair"
    "(x, f y z) : (0 x : a) * x"
    (Eval $ Ann (Pair (ifg "x") (Inf $ fg "f" :@: ifg "y" :@: ifg "z"))
                (TensPr Rig0 (ifg "a") (ib 0))
    )
  , SuccTest "Annotated unit elimination"
             "let x @ () = () : Unit in () : Unit"
             (Eval $ UnitElim (Ann Unit UnitType) Unit UnitType)
  , SuccTest "Annotated function application"
             "f x : a"
             (Eval $ Ann (Inf $ fg "f" :@: ifg "x") (ifg "a"))
  , SuccTest
    "Fst Eliminator"
    "let 0 fst = (\\ a b p. let z @ x,y = p in x : a) : (0 a: *) -> (0 b : (0 a' : a) -> *) -> (0 p : (0 x : a) * b x) -> a"
    (Let Rig0 "fst" $ Ann
      (Lam
        (Lam (Lam (Inf (PairElim (Bound 0) (Inf (Bound 1)) (Inf (Bound 3))))))
      )
      (Pi
        Rig0
        Star
        (Pi
          Rig0
          (Pi Rig0 (Inf (Bound 0)) Star)
          (Pi Rig0
              (TensPr Rig0 (Inf (Bound 1)) (Inf (Bound 1 :@: Inf (Bound 0))))
              (Inf (Bound 2))
          )
        )
      )
    )
  ]
 where
  fg  = Free . Global
  ifg = Inf . fg
  ib  = Inf . Bound

succTestSpec :: SuccTest -> SpecWith ()
succTestSpec (SuccTest d i r) =
  it d $ parse (parseStmt []) "test" i `shouldBe` Right r

spec :: Spec
spec = foldM (const succTestSpec) () succTests

