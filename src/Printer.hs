module Printer where

import           Text.PrettyPrint               ( text
                                                , sep
                                                , nest
                                                , Doc
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
  parensIf (p > 1) (cPrint 2 ii c <> text " :: " <> cPrint 0 ii ty)
iPrint _ ii (Bound k         ) = text (vars !! (ii - k - 1))
iPrint _ _  (Free  (Global s)) = text s
iPrint p ii (i :@: c) =
  parensIf (p > 2) (sep [iPrint 2 ii i, nest 2 (cPrint 3 ii c)])
iPrint _ _ x = text ("[" ++ show x ++ "]")

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
    <> text ") -> "
    , cPrint 0 (ii + 1) r
    ]
  )
cPrint p ii (Pair c c') =
  text "(" <> cPrint p ii c <> text ", " <> cPrint p ii c'
cPrint _p ii (TensPr q c c') =
  text "("
    <> text (show q)
    <> text " "
    <> text (vars !! ii)
    <> text " : "
    <> cPrint 0 ii c
    <> text ") * "
    <> cPrint 0 (ii + 1) c'
cPrint _p _ii Unit     = text "()"
cPrint _p _ii UnitType = text "Unit"

nestedForall :: Int -> [(ZeroOneMany, Int, CTerm)] -> CTerm -> Doc
nestedForall ii ds (Pi q d r) = nestedForall (ii + 1) ((q, ii, d) : ds) r
nestedForall ii ds x          = sep
  [ text "forall "
  <> sep
       [ parensIf
           True
           (  text (show q)
           <> text " "
           <> text (vars !! n)
           <> text " :: "
           <> cPrint 0 n d
           )
       | (q, n, d) <- reverse ds
       ]
  <> text " ."
  , cPrint 0 ii x
  ]

itprint :: Value -> Doc
itprint = text . show . quote0

