{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE FlexibleInstances #-}

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
  pretty :: a -> Doc

instance Pretty Doc where
  pretty = id

instance Pretty Text where
  pretty = PP.pretty

instance Pretty String where
  pretty = PP.pretty

instance Pretty Int where
  pretty = PP.pretty

instance Pretty Name where
  pretty (Global s ) = PP.pretty s
  pretty (Local s _) = PP.pretty s
  pretty x           = localVar "[" <> PP.pretty (show x) <> localVar "]"

instance Pretty ITerm where
  pretty = runPrinter $ iPrint 0

instance Pretty CTerm where
  pretty = runPrinter $ cPrint 0

instance Pretty Value where
  pretty = pretty . quote0

instance Pretty ZeroOneMany where
  pretty Zero = annotate (Term.color Term.Magenta <> Term.bold) "0"
  pretty One  = annotate (Term.color Term.Magenta <> Term.bold) "1"
  pretty Many = annotate (Term.color Term.Magenta <> Term.bold) "ω"

instance (Pretty n, Pretty q, Pretty t) => Pretty (Binding n q t) where
  pretty (Binding n q t) = align . group . PP.width (pretty q) $ \case
    0 -> rest
    _ -> " " <> rest
    where rest = var (pretty n) <> line <> ":" <+> pretty t

instance Pretty ExpectedType where
  pretty SomePi         = "_ -> _"
  pretty SomeMPair      = "_" <+> mult "*" <+> "_"
  pretty SomeAPair      = "_" <+> add "&" <+> "_"
  pretty SomeSum        = "_ ⊕ _"
  pretty (KnownType ty) = pretty ty

instance Pretty TypingError where
  pretty err = annotate (Term.color Term.Red <> Term.bold) "error:"
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
        [ pretty n <+> ":" <+> pretty ty
        , indent 2
          $   "Used"
          <+> pretty used
          <>  "-times, but available"
          <+> pretty avail
          <>  "-times."
        ]
    go (ErasureError t m) =
      "Type"
        <+> squotes (pretty t)
        <+> "used"
        <+> pretty m
        <>  "-times outside erased context."
    go (TypeClashError expected actual expr) = hardlines
      [ "Couldn't match expected type" <+> squotes (pretty expected)
      , indent 12 ("with actual type" <+> squotes (pretty actual))
      , "In the expression:" <+> pretty expr
      ]
    go (CheckError ty expr) = hardlines
      [ "Couldn't match expected type" <+> squotes (pretty ty)
      , "In the expression:" <+> pretty expr
      ]
    go (UnknownVarError n) = "Variable not in scope: " <> pretty (Free n)

-- | Convert the output of term evaluation into the 'Doc' form.
prettyResult :: ZeroOneMany -> Maybe String -> Value -> Value -> Doc
prettyResult q mn val ty =
  pretty q <+> maybe mempty ((<+> "= ") . var . pretty . pack) mn <> pretty
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

iPrint :: Int -> ITerm -> Printer Doc
iPrint p (Ann c c') = fmt <$> cPrint 2 c <*> cPrint 0 c'
 where
  fmt val ty = align . group . parensIf (p > 1) $ val <> line <> ":" <+> ty
iPrint _ (Bound k) = do
  name  <- asks (!! k)
  index <- asks $ length . filter (== name) . take k
  return $ pretty name <> if index > 0 then "@" <> pretty index else ""
iPrint _ (Free n ) = return $ pretty n
iPrint p (i :$: c) = fmt <$> iPrint 2 i <*> cPrint 3 c
  where fmt f x = parensIf (p > 2) . align $ sep [f, x]
iPrint p (MPairElim q z x y l i t) =
  fmt <$> iPrint 0 l <*> local (flip (foldr bind) [y, x]) (cPrint 0 i) <*> local
    (bind z)
    (cPrint 0 t)
 where
  fmt letPart inPart typePart = parensIf (p > 0) . align $ sep
    [ hsep
      [ mult "let"
      , pretty q
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
iPrint p (MUnitElim q x l i t) = fmt <$> iPrint 0 l <*> cPrint 0 i <*> local
  (bind x)
  (cPrint 0 t)
 where
  fmt letPart inPart typePart = parensIf (p > 0) . align $ sep
    [ hsep
      [ mult "let"
      , pretty q
      , var $ PP.pretty x
      , mult "@"
      , mult "()"
      , mult "="
      , letPart
      ]
    , mult "in" <+> inPart
    , mult ":" <+> typePart
    ]
iPrint p (Fst i) = parensIf (p > 0) . (add "fst" <+>) <$> iPrint 3 i
iPrint p (Snd i) = parensIf (p > 0) . (add "snd" <+>) <$> iPrint 3 i
iPrint p (SumElim q z i x c y c' c'') =
  fmt
    <$> iPrint 0 i
    <*> local (bind x) (cPrint 0 c)
    <*> local (bind y) (cPrint 0 c')
    <*> local (bind z) (cPrint 0 c'')
 where
  fmt s l r ty =
    parensIf (p > 0)
      $   hsep ["case", pretty q, var $ pretty z, "@", s, "of"]
      <+> align (sep ["{" <+> branches l r, "} :" <+> ty])
  branch ctr n body = ctr <+> var (pretty n) <+> "→" <+> body
  branches l r = align $ sep [branch "inl" x l <> ";", branch "inr" y r]

cPrint :: Int -> CTerm -> Printer Doc
cPrint p (Inf i  ) = iPrint p i
cPrint p (Lam x c) = parensIf (p > 0) <$> go [x] c
 where
  go xs (Lam x' c') = go (x' : xs) c'
  go xs c'          = fmt xs <$> local (flip (foldr bind) xs) (cPrint 0 c')
  fmt xs body =
    "λ" <> hsep (map (var . PP.pretty) $ reverse xs) <> "." <+> body
cPrint p (Pi q1 x1 c (Pi q2 x2 c' c'')) =
  parensIf (p > 0) <$> go [Binding x2 q2 c', Binding x1 q1 c] c''
 where
  go bs (Pi q x d body) = go (Binding x q d : bs) body
  go bs body            = do
    binds <-
      traverse
        (\(Binding n q d, prevBinds) -> fmtBind q n
          <$> local (flip (foldr bind) $ map bndName prevBinds) (cPrint 0 d)
        )
      . scanl1 (flip (\(newBind, _) -> (newBind, ) . uncurry (:)))
      . flip zip (repeat [])
      $ reverse bs
    bodyDoc <- local (flip (foldr bind) $ map bndName bs) (cPrint 0 body)
    return . align $ sep ["∀" <+> align (sep binds), "." <+> bodyDoc]
  fmtBind q n body = parens $ hsep [pretty q, var $ PP.pretty n, ":", body]
cPrint p (Pi q x c c') = cPrintDependent fmt x c c'
 where
  fmt n l r = align . group . parensIf (p > 0) $ sep
    ["(" <> pretty (Binding n q l) <> ")" <+> "→", r]
cPrint p (MPairType q x c c') = cPrintDependent fmt x c c'
 where
  fmt n l r = align . group . parensIf (p > 0) $ sep
    [mult "(" <> pretty (Binding n q l) <> mult ")" <+> mult "⊗", r]
cPrint p (APairType x c c') = cPrintDependent fmt x c c'
 where
  fmt n l r = align . group . parensIf (p > 0) $ sep
    [add "(" <> pretty (Binding @_ @Text n "" l) <> add ")" <+> add "&", r]
cPrint _ (MPair c c') = fmt <$> cPrint 0 c <*> cPrint 0 c'
  where fmt l r = mult "(" <> l <> mult "," <+> r <> mult ")"
cPrint _ (APair c c') = fmt <$> cPrint 0 c <*> cPrint 0 c'
  where fmt l r = add "⟨" <> l <> add "," <+> r <> add "⟩"
cPrint _ Universe       = return "𝘜"
cPrint _ MUnit          = return $ mult "()"
cPrint _ MUnitType      = return $ mult "𝟭ₘ"
cPrint _ AUnit          = return $ add "⟨⟩"
cPrint _ AUnitType      = return $ add "⊤"
cPrint p (SumL c      ) = parensIf (p > 0) . ("inl" <+>) <$> cPrint 3 c
cPrint p (SumR c      ) = parensIf (p > 0) . ("inr" <+>) <$> cPrint 3 c
cPrint p (SumType c c') = fmt <$> cPrint 0 c <*> cPrint 0 c'
  where fmt l r = parensIf (p > 0) $ l <+> "⊕" <+> r

cPrintDependent
  :: (BindingName -> Doc -> Doc -> Doc)
  -> BindingName
  -> CTerm
  -> CTerm
  -> Printer Doc
cPrintDependent fmt n l r =
  fmt n <$> cPrint 0 l <*> local (bind n) (cPrint 0 r)

mult, add, var, localVar :: Doc -> Doc
mult = annotate (Term.color Term.Blue <> Term.bold)
add = annotate (Term.color Term.Green <> Term.bold)
var = annotate Term.bold
localVar = annotate (Term.color Term.Yellow <> Term.bold)

