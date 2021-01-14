{-# OPTIONS_GHC -fno-warn-orphans #-}

module Printer
  ( render
  , pretty
  , renderRes
  ) where

import           Data.Text.Prettyprint.Doc      ( (<+>)
                                                , Doc
                                                , Pretty(pretty)
                                                , align
                                                , defaultLayoutOptions
                                                , layoutSmart
                                                , parens
                                                , sep
                                                )
import           Data.Text.Prettyprint.Doc.Render.String
                                                ( renderString )
import           Rig                            ( ZeroOneMany(..) )
import           Types

render :: Doc ann -> String
render = renderString . layoutSmart defaultLayoutOptions

renderRes :: Binding (Maybe String) ZeroOneMany Type -> Value -> String
renderRes bnd val =
  let
    rest =
      align $ sep
        [pretty (bndUsage bnd) <+> pretty val, ":" <+> pretty (bndType bnd)]
    outtext =
      render . maybe id ((<+>) . (<+> "=") . pretty) (bndName bnd) $ rest
  in
    outtext

var :: Int -> Doc a
var i =
  [ pretty $ c : n
  | n <- "" : map show [1 :: Integer ..]
  , c <- ['x', 'y', 'z'] ++ ['a' .. 'w']
  ]
  !! i

parensIf :: Bool -> Doc ann -> Doc ann
parensIf True  = parens
parensIf False = id

instance Pretty ITerm where
  pretty = iPrint 0 0

iPrint :: Int -> Int -> ITerm -> Doc ann
iPrint p ii (Ann c ty) =
  parensIf (p > 1) (cPrint 2 ii c <+> ":" <+> cPrint 0 ii ty)
iPrint _ ii (Bound k) = var (ii - k - 1)
iPrint _ _  (Free  n) = pretty n
iPrint p ii (i :@: c) =
  parensIf (p > 2) (align $ sep [iPrint 2 ii i, cPrint 3 ii c])
iPrint p ii (PairElim l i t) = parensIf
  (p > 0)
  (align $ sep
    [ "let"
    <+> var (ii + 2)
    <+> "@"
    <+> var ii
    <>  ","
    <+> var (ii + 1)
    <+> "="
    <+> iPrint 0 ii l
    , "in" <+> cPrint 0 (ii + 2) i <+> ":" <+> cPrint 0 (ii + 3) t
    ]
  )
iPrint p ii (MUnitElim l i t) = parensIf
  (p > 0)
  (sep
    [ "let" <+> var ii <+> "@" <+> "()" <+> "=" <+> iPrint 0 ii l
    , "in" <+> cPrint 0 ii i <+> ":" <+> cPrint 0 (ii + 1) t
    ]
  )
iPrint p ii (Fst i) = parensIf (p > 0) ("Fst" <+> iPrint 3 ii i)
iPrint p ii (Snd i) = parensIf (p > 0) ("Snd" <+> iPrint 3 ii i)

instance Pretty CTerm where
  pretty = cPrint 0 0

cPrint :: Int -> Int -> CTerm -> Doc ann
cPrint p ii (Inf i) = iPrint p ii i
cPrint p ii (Lam c) =
  parensIf (p > 0) ("\\" <+> var ii <+> "." <+> cPrint 0 (ii + 1) c)
cPrint _ _ Star = "*"
cPrint p ii (Pi q d (Pi q' d' r)) =
  parensIf (p > 0) (nestedForall (ii + 2) [(q', ii + 1, d'), (q, ii, d)] r)
cPrint p ii (Pi q d r) = parensIf
  (p > 0)
  (sep
    [ "(" <> pretty q <+> var ii <+> ":" <+> cPrint 0 ii d <> ")" <+> "->"
    , cPrint 0 (ii + 1) r
    ]
  )
cPrint _ ii (Pair c c') = "(" <> cPrint 0 ii c <> "," <+> cPrint 0 ii c' <> ")"
cPrint p ii (Tensor q c c') = parensIf
  (p > 0)
  (sep
    [ "(" <> pretty q <+> var ii <+> ":" <+> cPrint 0 ii c <> ")" <+> "*"
    , cPrint 0 (ii + 1) c'
    ]
  )
cPrint _ _ MUnit     = "()"
cPrint _ _ MUnitType = "MUnit"
cPrint _ ii (Angles c c') =
  "<" <> cPrint 0 ii c <> "," <+> cPrint 0 ii c' <> ">"
cPrint p ii (With c c') = parensIf
  (p > 0)
  (sep
    [ "(" <> var ii <+> ":" <+> cPrint 0 ii c <> ")" <+> "&"
    , cPrint 0 (ii + 1) c'
    ]
  )
cPrint _ _ AUnit     = "<>"
cPrint _ _ AUnitType = "AUnit"

nestedForall :: Int -> [(ZeroOneMany, Int, CTerm)] -> CTerm -> Doc ann
nestedForall ii ds (Pi q d r) = nestedForall (ii + 1) ((q, ii, d) : ds) r
nestedForall ii ds x          = align $ sep
  [ "forall"
  <+> align
        (sep
          [ parens $ pretty q <+> var n <+> ":" <+> cPrint 0 n d
          | (q, n, d) <- reverse ds
          ]
        )
  <+> "."
  , cPrint 0 ii x
  ]

instance Pretty Value where
  pretty = pretty . quote0

instance Pretty ZeroOneMany where
  pretty Zero = "0"
  pretty One  = "1"
  pretty Many = "w"

instance Pretty Name where
  pretty (Global s) = pretty s
  pretty x          = "[" <> pretty (show x) <> "]"

