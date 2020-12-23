module Printer
  ( iPrint
  , cPrint
  , vPrint
  ) where

import           Rig                            ( ZeroOneMany )
import           Text.PrettyPrint               ( Doc
                                                , nest
                                                , sep
                                                , text
                                                )
import qualified Text.PrettyPrint              as PP
                                                ( parens )
import           Types

vars :: [String]
vars =
  [ c : n
  | n <- "" : map show [1 :: Integer ..]
  , c <- ['x', 'y', 'z'] ++ ['a' .. 'w']
  ]

parensIf :: Bool -> Doc -> Doc
parensIf True  = PP.parens
parensIf False = id

iPrint :: Int -> Int -> ITerm -> Doc
iPrint p ii (Ann c ty) =
  parensIf (p > 1) (cPrint 2 ii c <> text " : " <> cPrint 0 ii ty)
iPrint _ ii (Bound k         ) = text (vars !! (ii - k - 1))
iPrint _ _  (Free  (Global s)) = text s
iPrint _ _  (Free  x         ) = text ("[" ++ show x ++ "]")
iPrint p ii (i :@: c) =
  parensIf (p > 2) (sep [iPrint 2 ii i, nest 2 (cPrint 3 ii c)])
iPrint p ii (PairElim l i t) = parensIf
  (p > 0)
  (sep
    [ text "let "
    <> text (vars !! (ii + 2))
    <> text " @ "
    <> text (vars !! ii)
    <> text ", "
    <> text (vars !! (ii + 1))
    <> text " = "
    <> iPrint 0 ii l
    , text "in " <> cPrint 0 (ii + 2) i <> text " : " <> cPrint 0 (ii + 3) t
    ]
  )
iPrint p ii (MUnitElim l i t) = parensIf
  (p > 0)
  (sep
    [ text "let " <> text (vars !! ii) <> text " @ () =" <> iPrint 0 ii l
    , text "in " <> cPrint 0 ii i <> text " : " <> cPrint 0 (ii + 1) t
    ]
  )
iPrint p ii (Fst i) = parensIf (p > 0) (text "Fst " <> iPrint 3 ii i)
iPrint p ii (Snd i) = parensIf (p > 0) (text "Snd " <> iPrint 3 ii i)

cPrint :: Int -> Int -> CTerm -> Doc
cPrint p ii (Inf i) = iPrint p ii i
cPrint p ii (Lam c) = parensIf
  (p > 0)
  (text "\\ " <> text (vars !! ii) <> text ". " <> cPrint 0 (ii + 1) c)
cPrint _ _ Star = text "*"
cPrint p ii (Pi q d (Pi q' d' r)) =
  parensIf (p > 0) (nestedForall (ii + 2) [(q', ii + 1, d'), (q, ii, d)] r)
cPrint p ii (Pi q d r) = parensIf
  (p > 0)
  (sep
    [ text "("
    <> text (show q)
    <> text " "
    <> text (vars !! ii)
    <> text " : "
    <> cPrint 0 ii d
    <> text ") ->"
    , cPrint 0 (ii + 1) r
    ]
  )
cPrint _ ii (Pair c c') =
  text "(" <> cPrint 0 ii c <> text ", " <> cPrint 0 ii c' <> text ")"
cPrint p ii (Tensor q c c') = parensIf
  (p > 0)
  (sep
    [ text "("
    <> text (show q)
    <> text " "
    <> text (vars !! ii)
    <> text " : "
    <> cPrint 0 ii c
    <> text ") *"
    , cPrint 0 (ii + 1) c'
    ]
  )
cPrint _ _ MUnit     = text "()"
cPrint _ _ MUnitType = text "MUnit"
cPrint _ ii (Angles c c') =
  text "<" <> cPrint 0 ii c <> text ", " <> cPrint 0 ii c' <> text ">"
cPrint p ii (With c c') = parensIf
  (p > 0)
  (sep
    [ text "(" <> text (vars !! ii) <> text " : " <> cPrint 0 ii c <> text ") &"
    , cPrint 0 (ii + 1) c'
    ]
  )
cPrint _ _ AUnit     = text "<>"
cPrint _ _ AUnitType = text "AUnit"

nestedForall :: Int -> [(ZeroOneMany, Int, CTerm)] -> CTerm -> Doc
nestedForall ii ds (Pi q d r) = nestedForall (ii + 1) ((q, ii, d) : ds) r
nestedForall ii ds x          = sep
  [ text "forall "
  <> sep
       [ PP.parens
         $  text (show q)
         <> text " "
         <> text (vars !! n)
         <> text " : "
         <> cPrint 0 n d
       | (q, n, d) <- reverse ds
       ]
  <> text " ."
  , cPrint 0 ii x
  ]

vPrint :: Value -> Doc
vPrint = cPrint 0 0 . quote0

