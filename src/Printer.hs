{-# OPTIONS_GHC -fno-warn-orphans #-}

module Printer
  ( PrettyAnsi
  , (<+>)
  , addAnn
  , hardlines
  , multAnn
  , render
  , renderErr
  , renderRes
  , renderTest
  , prettyAnsi
  ) where

import           Data.List                      ( intersperse )
import           Data.Text                      ( Text )
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Render.String
                                                ( renderString )
import qualified Data.Text.Prettyprint.Doc.Render.Terminal
                                               as Term
import           Rig                            ( ZeroOneMany(..) )
import           Types

instance Pretty Name where
  pretty (Global s) = pretty s
  pretty x          = "[" <> pretty (show x) <> "]"

class PrettyAnsi a where
  prettyAnsi :: a -> Doc Term.AnsiStyle

instance PrettyAnsi Text where
  prettyAnsi = pretty

instance PrettyAnsi ITerm where
  prettyAnsi = iPrint 0 0

instance PrettyAnsi Value where
  prettyAnsi = prettyAnsi . quote0

instance PrettyAnsi ZeroOneMany where
  prettyAnsi Zero = annotate (Term.color Term.Magenta <> Term.bold) "0"
  prettyAnsi One  = annotate (Term.color Term.Magenta <> Term.bold) "1"
  prettyAnsi Many = annotate (Term.color Term.Magenta <> Term.bold) "w"

instance PrettyAnsi TypeError where
  prettyAnsi (MultiplicityError loc es) =
    hardlines
      $ (  "Mismatched multiplicities"
        <> maybe emptyDoc ((" " <>) . parens . pretty) loc
        <> ":"
        )
      : map (indent 2) (concatMap errInfo es)
   where
    errInfo (n, ty, used, avail) =
      [ pretty n <+> ":" <+> prettyAnsi ty
      , indent 2
        $   "Used"
        <+> prettyAnsi used
        <>  "-times, but available"
        <+> prettyAnsi avail
        <>  "-times."
      ]
  prettyAnsi (ErasureError t m) =
    "Type"
      <+> squotes (prettyAnsi t)
      <+> "used"
      <+> prettyAnsi m
      <>  "-times outside erased context."
  prettyAnsi (InferenceError expected actual expr) = hardlines
    [ "Couldn't match expected type" <+> squotes expected
    , indent 12 ("with actual type" <+> squotes (prettyAnsi actual))
    , "In the expression:" <+> prettyAnsi expr
    ]
  prettyAnsi (CheckError ty expr) = hardlines
    [ "Could't match expected type" <+> squotes (prettyAnsi ty)
    , "In the expression:" <+> prettyAnsi expr
    ]
  prettyAnsi (UnknownVarError n) =
    "Variable not in scope: " <> prettyAnsi (Free n)

instance Show TypeError where
  show = renderString . layoutPretty (LayoutOptions Unbounded) . prettyAnsi

render :: Doc Term.AnsiStyle -> Text
render = Term.renderStrict . layoutSmart defaultLayoutOptions

renderErr :: Doc Term.AnsiStyle -> Text
renderErr =
  Term.renderStrict
    . layoutSmart defaultLayoutOptions
    . (annotate (Term.color Term.Red <> Term.bold) "error:" <+>)
    . align

hardlines :: [Doc ann] -> Doc ann
hardlines = mconcat . intersperse hardline

renderBinding
  :: Maybe String -> Binding Value ZeroOneMany Type -> Doc Term.AnsiStyle
renderBinding name (Binding val q ty) = (assign <>) . align $ sep ann
 where
  ann    = [prettyAnsi q <+> prettyAnsi val, ":" <+> prettyAnsi ty]
  assign = maybe mempty (((<+> "= ") . annotate Term.bold) . pretty) name

renderRes :: Maybe String -> Binding Value ZeroOneMany Type -> Text
renderRes = (render .) . renderBinding

renderTest :: Maybe String -> Binding Value ZeroOneMany Type -> String
renderTest =
  ((renderString . layoutPretty (LayoutOptions Unbounded) . group) .)
    . renderBinding

var :: Int -> Doc ann
var =
  pretty
    . ([ c : n
       | n <- "" : map show [1 :: Integer ..]
       , c <- ['x', 'y', 'z'] ++ ['a' .. 'w']
       ] !!
      )

parensIf :: Bool -> Doc ann -> Doc ann
parensIf True  = parens
parensIf False = id

iPrint :: Int -> Int -> ITerm -> Doc Term.AnsiStyle
iPrint p ii (Ann c ty) =
  parensIf (p > 1) (cPrint 2 ii c <+> ":" <+> cPrint 0 ii ty)
iPrint _ ii (Bound k) = var (ii - k - 1)
iPrint _ _  (Free  n) = pretty n
iPrint p ii (i :$: c) =
  parensIf (p > 2) (align $ sep [iPrint 2 ii i, cPrint 3 ii c])
iPrint p ii (PairElim l i t) = parensIf
  (p > 0)
  (align $ sep
    [ multAnn "let"
    <+> varAnn (ii + 2)
    <+> multAnn "@"
    <+> varAnn ii
    <>  multAnn ","
    <+> varAnn (ii + 1)
    <+> multAnn "="
    <+> iPrint 0 ii l
    , multAnn "in"
    <+> cPrint 0 (ii + 2) i
    <+> multAnn ":"
    <+> cPrint 0 (ii + 3) t
    ]
  )
iPrint p ii (MUnitElim l i t) = parensIf
  (p > 0)
  (sep
    [ multAnn "let"
    <+> varAnn ii
    <+> multAnn "@"
    <+> multAnn "()"
    <+> multAnn "="
    <+> iPrint 0 ii l
    , multAnn "in" <+> cPrint 0 ii i <+> multAnn ":" <+> cPrint 0 (ii + 1) t
    ]
  )
iPrint p ii (Fst i) = parensIf (p > 0) (addAnn "fst" <+> iPrint 3 ii i)
iPrint p ii (Snd i) = parensIf (p > 0) (addAnn "snd" <+> iPrint 3 ii i)

instance PrettyAnsi CTerm where
  prettyAnsi = cPrint 0 0

cPrint :: Int -> Int -> CTerm -> Doc Term.AnsiStyle
cPrint p ii (Inf i)  = iPrint p ii i
cPrint p ii (Lam c)  = parensIf (p > 0) (lambdas ii 1 c)
cPrint _ _  Universe = "U"
cPrint p ii (Pi q d (Pi q' d' r)) =
  parensIf (p > 0) (nestedForall (ii + 2) [(q', ii + 1, d'), (q, ii, d)] r)
cPrint p ii (Pi q d r) = parensIf
  (p > 0)
  (sep
    [ "("
    <>  prettyAnsi q
    <+> varAnn ii
    <+> ":"
    <+> cPrint 0 ii d
    <>  ")"
    <+> "->"
    , cPrint 0 (ii + 1) r
    ]
  )
cPrint _ ii (Pair c c') =
  multAnn "(" <> cPrint 0 ii c <> multAnn "," <+> cPrint 0 ii c' <> multAnn ")"
cPrint p ii (Tensor q c c') = parensIf
  (p > 0)
  (sep
    [ multAnn "("
    <>  prettyAnsi q
    <+> varAnn ii
    <+> ":"
    <+> cPrint 0 ii c
    <>  multAnn ")"
    <+> multAnn "*"
    , cPrint 0 (ii + 1) c'
    ]
  )
cPrint _ _ MUnit     = multAnn "()"
cPrint _ _ MUnitType = multAnn "I"
cPrint _ ii (Angles c c') =
  addAnn "<" <> cPrint 0 ii c <> addAnn "," <+> cPrint 0 ii c' <> addAnn ">"
cPrint p ii (With c c') = parensIf
  (p > 0)
  (sep
    [ addAnn "(" <> varAnn ii <+> ":" <+> cPrint 0 ii c <> addAnn ")" <+> addAnn
      "&"
    , cPrint 0 (ii + 1) c'
    ]
  )
cPrint _ _ AUnit     = addAnn "<>"
cPrint _ _ AUnitType = addAnn "T"

multAnn :: Doc Term.AnsiStyle -> Doc Term.AnsiStyle
multAnn = annotate (Term.color Term.Blue <> Term.bold)

addAnn :: Doc Term.AnsiStyle -> Doc Term.AnsiStyle
addAnn = annotate (Term.color Term.Green <> Term.bold)

varAnn :: Int -> Doc Term.AnsiStyle
varAnn = annotate Term.bold . var

lambdas :: Int -> Int -> CTerm -> Doc Term.AnsiStyle
lambdas ii depth (Lam c) = lambdas ii (depth + 1) c
lambdas ii depth c =
  "λ"
    <>  hsep (map varAnn [ii .. ii + depth - 1])
    <>  "."
    <+> cPrint 0 (ii + depth) c

nestedForall
  :: Int -> [(ZeroOneMany, Int, CTerm)] -> CTerm -> Doc Term.AnsiStyle
nestedForall ii ds (Pi q d r) = nestedForall (ii + 1) ((q, ii, d) : ds) r
nestedForall ii ds x          = align $ sep
  [ "∀"
  <+> align
        (sep
          [ parens $ prettyAnsi q <+> varAnn n <+> ":" <+> cPrint 0 n d
          | (q, n, d) <- reverse ds
          ]
        )
  <+> "."
  , cPrint 0 ii x
  ]

