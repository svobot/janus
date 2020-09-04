module ParseSpec
  ( spec
  )
where

import           Test.Hspec
import           Parser
import           Types
import           Text.Parsec                    ( parse )
import           Control.Monad                  ( foldM )

data SuccTest = SuccTest String String Stmt

succTests :: [SuccTest]
succTests =
  [ SuccTest
    "Left associative application"
    "f x y"
    (Eval $ (Free (Global "f") :@: Inf (Free $ Global "x")) :@: Inf
      (Free $ Global "y")
    )
  , SuccTest
    "Annotated identity function"
    "(\\ a x . x) : (0 a : *) -> (1 x : a) -> a"
    (Eval $ Ann (Lam (Lam (Inf (Bound 0))))
                (Pi Rig0 Star (Pi Rig1 (Inf (Bound 0)) (Inf (Bound 1))))
    )
  , SuccTest
    "Dependent assumption"
    "assume (0 MyBool : *) (1 MyFalse : MyBool)"
    (Assume
      [(Rig0, "MyBool", Star), (Rig1, "MyFalse", Inf (Free (Global "MyBool")))]
    )
  ]

succTestSpec :: SuccTest -> SpecWith ()
succTestSpec (SuccTest d i r) =
  it d $ parse (parseStmt []) "test" i `shouldBe` Right r

spec :: Spec
spec = describe "Parser" $ do
  foldM (const succTestSpec) () succTests

