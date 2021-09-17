{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}

-- | Specifies how to pretty-print expressions for display.
module Janus.Pretty
  ( Doc
  , Pretty(..)
  , render
  , renderString
  , prettyResult
  ) where

import           Control.Monad.Reader           ( MonadReader(local)
                                                , Reader
                                                , asks
                                                , runReader
                                                )
import           Data.List                      ( intersperse )
import           Data.Text                      ( Text
                                                , pack
                                                )
import           Janus.Evaluation
import           Janus.Infer
import           Janus.Judgment
import           Janus.Semiring                 ( ZeroOneMany(..) )
import           Janus.Style
import           Janus.Syntax
import qualified Prettyprinter                 as PP
import           Prettyprinter           hiding ( Doc
                                                , Pretty(..)
                                                )
import qualified Prettyprinter.Render.String   as PPS
import qualified Prettyprinter.Render.Terminal as Term

-- | Abstract type of documents annotated with the ANSI terminal colors.
type Doc = PP.Doc Term.AnsiStyle

-- | Conversion to 'Doc'.
class Pretty a where
  pretty :: Style -> a -> Doc

instance Pretty Doc where
  pretty = const id

instance Pretty Text where
  pretty = const PP.pretty

instance Pretty String where
  pretty = const PP.pretty

instance Pretty Int where
  pretty = const PP.pretty

instance Pretty Name where
  pretty _ (Global n ) = PP.pretty n
  pretty _ (Local n _) = PP.pretty n
  pretty _ x           = localVar "[" <> PP.pretty (show x) <> localVar "]"

instance Pretty ITerm where
  pretty s = runPrinter $ iPrint s 0

instance Pretty CTerm where
  pretty s = runPrinter $ cPrint s 0

instance Pretty Value where
  pretty s = pretty s . quote0

instance Pretty ZeroOneMany where
  pretty _ Zero = annotate (Term.color Term.Magenta <> Term.bold) "0"
  pretty _ One  = annotate (Term.color Term.Magenta <> Term.bold) "1"
  pretty Style {..} Many =
    annotate (Term.color Term.Magenta <> Term.bold) (PP.pretty stMany)

instance (Pretty n, Pretty q, Pretty t) => Pretty (Binding n q t) where
  pretty s (Binding n q t) = align . group . PP.width (pretty s q) $ \case
    0 -> rest
    _ -> " " <> rest
    where rest = var (pretty s n) <> line <> ":" <+> pretty s t

instance Pretty ExpectedType where
  pretty Style {..} SomePi         = "_" <+> PP.pretty stArrow <+> "_"
  pretty Style {..} SomeMPair = "_" <+> mult (PP.pretty stMPairTypeOp) <+> "_"
  pretty _          SomeAPair      = "_" <+> add "&" <+> "_"
  pretty Style {..} SomeSum        = "_" <+> PP.pretty stSumTypeOp <+> "_"
  pretty s          (KnownType ty) = pretty s ty

instance Pretty TypingError where
  pretty s err = annotate (Term.color Term.Red <> Term.bold) "error:"
    <+> align (go err)
   where
    go (UsageError loc es) =
      hardlines
        $ (  "Mismatched multiplicities"
          <> maybe emptyDoc ((" " <>) . parens . PP.pretty) loc
          <> ":"
          )
        : map (indent 2) (concatMap errInfo es)
     where
      errInfo (n, ty, used, avail) =
        [ pretty s n <+> ":" <+> pretty s ty
        , indent 2
          $   "Used"
          <+> pretty s used
          <>  "-times, but available"
          <+> pretty s avail
          <>  "-times."
        ]
    go (ErasureError t m) =
      "Type"
        <+> squotes (pretty s t)
        <+> "used"
        <+> pretty s m
        <>  "-times outside erased context."
    go (TypeClashError expected actual expr) = hardlines
      [ "Couldn't match expected type" <+> squotes (pretty s expected)
      , indent 12 ("with actual type" <+> squotes (pretty s actual))
      , "In the expression:" <+> pretty s expr
      ]
    go (CheckError ty expr) = hardlines
      [ "Couldn't match expected type" <+> squotes (pretty s ty)
      , "In the expression:" <+> pretty s expr
      ]
    go (UnknownVarError n) = "Variable not in scope: " <> pretty s (Free n)

-- | Convert the output of term evaluation into the 'Doc' form.
prettyResult :: Style -> ZeroOneMany -> Maybe String -> Value -> Value -> Doc
prettyResult s q mn val ty =
  pretty s q <+> maybe mempty ((<+> "= ") . var . pretty s . pack) mn <> pretty
    s
    (Ann (quote0 val) (quote0 ty))

-- | Render the document into 'Text' containing the ANSI color escape sequences.
-- The output of this function is intended to be displayed to the user.
render :: Doc -> Text
render = Term.renderStrict . layoutSmart defaultLayoutOptions

-- | Render the document into 'String' with the ANSI color escape sequences
-- stripped. The output of this function is intended to be used in the
-- interpreter tests where color would be unnecessarily complicating things.
renderString :: Doc -> String
renderString = PPS.renderString . layoutSmart defaultLayoutOptions . unAnnotate

hardlines :: [Doc] -> Doc
hardlines = mconcat . intersperse hardline

parensIf :: Bool -> Doc -> Doc
parensIf True  = parens
parensIf False = id

type NameEnv = [BindingName]

-- | 'Reader' environment tracks the bound variables. Shadowed variables are
-- appended with an index to distinguish them from more tightly bound variables.
type Printer = Reader NameEnv

-- | Convert a term into a 'Doc'.
runPrinter :: (a -> Printer Doc) -> a -> Doc
runPrinter printer = flip runReader [] . printer

-- | Add a new name to the list of bound variables.
bind :: BindingName -> NameEnv -> NameEnv
bind b bs = b : bs

iPrint :: Style -> Int -> ITerm -> Printer Doc
iPrint s p (Ann c c') = fmt <$> cPrint s 2 c <*> cPrint s 0 c'
 where
  fmt val ty = align . group . parensIf (p > 1) $ val <> line <> ":" <+> ty
iPrint s _ (Bound k) = do
  name  <- asks (!! k)
  index <- asks $ length . filter (== name) . take k
  return $ pretty s name <> if index > 0 then "@" <> pretty s index else ""
iPrint s _ (Free n ) = return $ pretty s n
iPrint s p (i :$: c) = fmt <$> iPrint s 2 i <*> cPrint s 3 c
  where fmt f x = parensIf (p > 2) . align $ sep [f, x]
iPrint s p (MPairElim q z x y l i t) =
  fmt
    <$> iPrint s 0 l
    <*> local (flip (foldr bind) [y, x]) (cPrint s 0 i)
    <*> local (bind z)                   (cPrint s 0 t)
 where
  fmt letPart inPart typePart = parensIf (p > 0) . align $ sep
    [ hsep
      [ mult "let"
      , pretty s q
      , var (PP.pretty z)
      , mult "@"
      , mult "(" <> var (PP.pretty x) <> mult ","
      , var (PP.pretty y) <> mult ")"
      , mult "="
      , letPart
      ]
    , mult "in" <+> inPart
    , mult ":" <+> typePart
    ]
iPrint s p (MUnitElim q x l i t) =
  fmt <$> iPrint s 0 l <*> cPrint s 0 i <*> local (bind x) (cPrint s 0 t)
 where
  fmt letPart inPart typePart = parensIf (p > 0) . align $ sep
    [ hsep
      [ mult "let"
      , pretty s q
      , var $ PP.pretty x
      , mult "@"
      , mult "()"
      , mult "="
      , letPart
      ]
    , mult "in" <+> inPart
    , mult ":" <+> typePart
    ]
iPrint s p (Fst i) = parensIf (p > 0) . (add "fst" <+>) <$> iPrint s 3 i
iPrint s p (Snd i) = parensIf (p > 0) . (add "snd" <+>) <$> iPrint s 3 i
iPrint s@Style {..} p (SumElim q z i x c y c' c'') =
  fmt
    <$> iPrint s 0 i
    <*> local (bind x) (cPrint s 0 c)
    <*> local (bind y) (cPrint s 0 c')
    <*> local (bind z) (cPrint s 0 c'')
 where
  fmt sumTerm l r ty =
    parensIf (p > 0)
      $   hsep ["case", pretty s q, var $ pretty s z, "@", sumTerm, "of"]
      <+> align (sep ["{" <+> branches l r, "} :" <+> ty])
  branch ctr n body = ctr <+> var (pretty s n) <+> PP.pretty stArrow <+> body
  branches l r = align $ sep [branch "inl" x l <> ";", branch "inr" y r]

cPrint :: Style -> Int -> CTerm -> Printer Doc
cPrint s            p (Inf i  ) = iPrint s p i
cPrint s@Style {..} p (Lam x c) = parensIf (p > 0) <$> go [x] c
 where
  go xs (Lam x' c') = go (x' : xs) c'
  go xs c'          = fmt xs <$> local (flip (foldr bind) xs) (cPrint s 0 c')
  fmt xs body =
    PP.pretty stLambda
      <>  hsep (map (var . PP.pretty) $ reverse xs)
      <>  "."
      <+> body
cPrint s@Style {..} p (Pi q1 x1 c (Pi q2 x2 c' c'')) =
  parensIf (p > 0) <$> go [Binding x2 q2 c', Binding x1 q1 c] c''
 where
  go bs (Pi q x d body) = go (Binding x q d : bs) body
  go bs body            = do
    binds <-
      traverse
        (\(Binding n q d, prevBinds) -> fmtBind q n
          <$> local (flip (foldr bind) $ map bndName prevBinds) (cPrint s 0 d)
        )
      . scanl1 (flip (\(newBind, _) -> (newBind, ) . uncurry (:)))
      . flip zip (repeat [])
      $ reverse bs
    bodyDoc <- local (flip (foldr bind) $ map bndName bs) (cPrint s 0 body)
    return . align $ sep
      [PP.pretty stForall <+> align (sep binds), "." <+> bodyDoc]
  fmtBind q n body = parens $ hsep [pretty s q, var $ PP.pretty n, ":", body]
cPrint s@Style {..} p (Pi q x c c') = cPrintDependent s fmt x c c'
 where
  fmt n l r = align . group . parensIf (p > 0) $ sep
    ["(" <> pretty s (Binding n q l) <> ")" <+> PP.pretty stArrow, r]
cPrint s@Style {..} p (MPairType q x c c') = cPrintDependent s fmt x c c'
 where
  fmt n l r = align . group . parensIf (p > 0) $ sep
    [ mult "(" <> pretty s (Binding n q l) <> mult ")" <+> mult
      (PP.pretty stMPairTypeOp)
    , r
    ]
cPrint s p (APairType x c c') = cPrintDependent s fmt x c c'
 where
  fmt n l r = align . group . parensIf (p > 0) $ sep
    [add "(" <> pretty s (Binding @_ @Text n "" l) <> add ")" <+> add "&", r]
cPrint s _ (MPair c c') = fmt <$> cPrint s 0 c <*> cPrint s 0 c'
  where fmt l r = mult "(" <> l <> mult "," <+> r <> mult ")"
cPrint s@Style {..} _ (APair c c') = fmt <$> cPrint s 0 c <*> cPrint s 0 c'
 where
  fmt l r = add (PP.pretty stAPairOpen) <> l <> add "," <+> r <> add
    (PP.pretty stAPairClose)
cPrint Style {..}   _ Universe       = return $ PP.pretty stUniverse
cPrint _            _ MUnit          = return $ mult "()"
cPrint Style {..}   _ MUnitType      = return . mult $ PP.pretty stMUnitType
cPrint Style {..}   _ AUnit          = return . add $ PP.pretty stAUnit
cPrint Style {..}   _ AUnitType      = return . add $ PP.pretty stAUnitType
cPrint s p (SumL c) = parensIf (p > 0) . ("inl" <+>) <$> cPrint s 3 c
cPrint s p (SumR c) = parensIf (p > 0) . ("inr" <+>) <$> cPrint s 3 c
cPrint s@Style {..} p (SumType c c') = fmt <$> cPrint s 0 c <*> cPrint s 0 c'
  where fmt l r = parensIf (p > 0) $ l <+> PP.pretty stSumTypeOp <+> r

cPrintDependent
  :: Style
  -> (BindingName -> Doc -> Doc -> Doc)
  -> BindingName
  -> CTerm
  -> CTerm
  -> Printer Doc
cPrintDependent s fmt n l r =
  fmt n <$> cPrint s 0 l <*> local (bind n) (cPrint s 0 r)

mult, add, var, localVar :: Doc -> Doc
mult = annotate (Term.color Term.Blue <> Term.bold)
add = annotate (Term.color Term.Green <> Term.bold)
var = annotate Term.bold
localVar = annotate (Term.color Term.Yellow <> Term.bold)

