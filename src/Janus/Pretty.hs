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

import           Control.Monad                  ( ap
                                                , liftM2
                                                )
import           Control.Monad.Reader           ( MonadReader(local)
                                                , Reader
                                                , asks
                                                , runReader
                                                )
import           Control.Monad.Writer.Strict    ( MonadWriter(tell)
                                                , Writer
                                                , runWriter
                                                )
import           Data.List                      ( intersperse )
import qualified Data.Set                      as Set
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

instance Pretty Name where
  pretty (Global s) = PP.pretty s
  pretty x          = localVar "[" <> PP.pretty (show x) <> localVar "]"

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

-- | 'Printer' monad keeps track of used names in a term and makes sure that new
-- names created when replacing De Bruijn indices of bound variables are unique.
type Printer doc = Writer FreeVars (Reader (NameEnv doc) doc)

type FreeVars = Set.Set String

data NameEnv doc = NameEnv
  { fresh :: [doc]
  , bound :: [doc]
  }

-- | Convert a term into a 'Doc'.
--
-- 'Writer' first accumulates names of free variables that are used in
-- the printed document and then creates a 'Reader' environment which
-- distributes non-clashing names to bound variables that are being converted
-- from De Bruijn indices.
runPrinter :: (a -> Printer Doc) -> a -> Doc
runPrinter printer term = runReader r (NameEnv freshNames [])
 where
  (r, freeVars) = runWriter (printer term)
  -- Filter the free variables that occur in the term out of the names that can
  -- be used for bound variables.
  freshNames =
    [ PP.pretty $ c : n
    | n <- "" : map show [1 :: Int ..]
    , c <- ['x', 'y', 'z'] ++ ['a' .. 'v']
    , (c : n) `Set.notMember` freeVars
    ]

-- | Skip binding one variable in the 'Reader' environment.
skip :: Int -> NameEnv a -> NameEnv a
skip i env = env { fresh = drop i $ fresh env }

-- | Make a new 'Reader' environment with a new variable bound.
bind :: NameEnv a -> NameEnv a
bind (NameEnv (new : fs) bs) = NameEnv fs (new : bs)
bind _                       = error "internal: No new variable name available."

-- | Make a new 'Reader' environment with multiple new variables bound.
bindMany :: Int -> NameEnv a -> NameEnv a
bindMany n (NameEnv as bs) = NameEnv (drop n as) (reverse (take n as) ++ bs)

iPrint :: Int -> ITerm -> Printer Doc
iPrint p (Ann c c') = (<*>) . (fmt <$>) <$> cPrint 2 c <*> cPrint 0 c'
 where
  fmt val ty = align . group . parensIf (p > 1) $ val <> line <> ":" <+> ty
iPrint _ (Bound k) = return . asks $ (!! k) . bound
iPrint _ (Free  n) = do
  case n of
    Global s -> tell $ Set.singleton s
    _        -> return ()
  return . return $ pretty n
iPrint p (i :$: c) = (<*>) . (fmt <$>) <$> iPrint 2 i <*> cPrint 3 c
  where fmt f x = parensIf (p > 2) . align $ sep [f, x]
iPrint p (MPairElim l i t) = do
  letPart  <- iPrint 0 l
  inPart   <- cPrint 0 i
  typePart <- cPrint 0 t
  return
    $   asks (fmt . fresh)
    <*> letPart
    <*> local (bindMany 2)    inPart
    <*> local (bind . skip 2) typePart
 where
  fmt names letPart inPart typePart = parensIf (p > 0) . align $ sep
    [ mult "let"
    <+> var (names !! 2)
    <+> mult "@"
    <+> var (head names)
    <>  mult ","
    <+> var (names !! 1)
    <+> mult "="
    <+> letPart
    , mult "in" <+> inPart <+> mult ":" <+> typePart
    ]
iPrint p (MUnitElim l i t) = do
  letPart  <- iPrint 0 l
  inPart   <- cPrint 0 i
  typePart <- cPrint 0 t
  return
    $   asks (fmt . head . fresh)
    <*> letPart
    <*> inPart
    <*> local bind typePart
 where
  fmt name letPart inPart typePart = parensIf (p > 0) $ sep
    [ mult "let"
    <+> var name
    <+> mult "@"
    <+> mult "()"
    <+> mult "="
    <+> letPart
    , mult "in" <+> inPart <+> mult ":" <+> typePart
    ]
iPrint p (Fst i) = (parensIf (p > 0) . (add "fst" <+>) <$>) <$> iPrint 3 i
iPrint p (Snd i) = (parensIf (p > 0) . (add "snd" <+>) <$>) <$> iPrint 3 i
iPrint p (SumElim q i c c' c'') = do
  s         <- iPrint 0 i
  leftPart  <- cPrint 0 c
  rightPart <- cPrint 0 c'
  typePart  <- cPrint 0 c''
  return $ do
    (x, y, z) <- asks (ap (liftM2 (,,) head (!! 1)) (!! 2) . fresh)
    fmt x y z
      <$> s
      <*> local (skip 2 . bind)          leftPart
      <*> local (skip 1 . bind . skip 1) rightPart
      <*> local (bind . skip 2)          typePart
 where
  fmt x y z s l r ty =
    parensIf (p > 0) $ hsep ["case", pretty q, var z, "@", s, "of"] <+> align
      (sep ["{" <+> branches x y l r, "} :" <+> ty])
  branch ctr n body = ctr <+> var n <+> "→" <+> body
  branches x y l r = align $ sep [branch "inl" x l <> ";", branch "inr" y r]

cPrint :: Int -> CTerm -> Printer Doc
cPrint p (Inf i) = iPrint p i
cPrint p (Lam c) = (parensIf (p > 0) <$>) <$> go 0 c
 where
  go depth (Lam c') = go (depth + 1) c'
  go depth c'       = do
    body <- cPrint 0 c'
    return $ asks (fmt depth . fresh) <*> local (bindMany $ depth + 1) body
  fmt depth names body = do
    "λ" <> hsep (map (var . (names !!)) [0 .. depth]) <> "." <+> body
cPrint p (Pi q1 d1 (Pi q2 d2 r)) =
  (parensIf (p > 0) <$>) <$> go [(q2, d2), (q1, d1)] r
 where
  go ds (Pi q d x) = go ((q, d) : ds) x
  go ds x          = do
    let bindCount = length ds
    binds <- mapM
      (\(depth, (q, d)) -> do
        ty <- cPrint 0 d
        return
          .   local (bindMany depth)
          $   asks (fmtBind q . head . fresh)
          <*> local (skip $ bindCount - depth) ty
      )
      (zip [0 ..] $ reverse ds)
    body <- cPrint 0 x
    return $ do
      bindsDoc <- sequence binds
      bodyDoc  <- local (bindMany bindCount) body
      return . align $ sep ["∀" <+> align (sep bindsDoc), "." <+> bodyDoc]
  fmtBind q name body = parens $ pretty q <+> var name <+> ":" <+> body
cPrint p (Pi q c c') = cPrintDependent fmt c c'
 where
  fmt name l r = align . group . parensIf (p > 0) $ sep
    ["(" <> pretty (Binding name q l) <> ")" <+> "→", r]
cPrint p (MPairType q c c') = cPrintDependent fmt c c'
 where
  fmt name l r = align . group . parensIf (p > 0) $ sep
    [mult "(" <> pretty (Binding name q l) <> mult ")" <+> mult "⊗", r]
cPrint p (APairType c c') = cPrintDependent fmt c c'
 where
  fmt name l r = align . group . parensIf (p > 0) $ sep
    [add "(" <> pretty (Binding @_ @Text name "" l) <> add ")" <+> add "&", r]
cPrint _ (MPair c c') = (<*>) . (fmt <$>) <$> cPrint 0 c <*> cPrint 0 c'
  where fmt l r = mult "(" <> l <> mult "," <+> r <> mult ")"
cPrint _ (APair c c') = (<*>) . (fmt <$>) <$> cPrint 0 c <*> cPrint 0 c'
  where fmt l r = add "⟨" <> l <> add "," <+> r <> add "⟩"
cPrint _ Universe       = return . return $ "𝘜"
cPrint _ MUnit          = return . return $ mult "()"
cPrint _ MUnitType      = return . return $ mult "𝟭ₘ"
cPrint _ AUnit          = return . return $ add "⟨⟩"
cPrint _ AUnitType      = return . return $ add "⊤"
cPrint p (SumL c      ) = (parensIf (p > 0) . ("inl" <+>) <$>) <$> cPrint 3 c
cPrint p (SumR c      ) = (parensIf (p > 0) . ("inr" <+>) <$>) <$> cPrint 3 c
cPrint p (SumType c c') = (<*>) . (fmt <$>) <$> cPrint 0 c <*> cPrint 0 c'
  where fmt l r = parensIf (p > 0) $ l <+> "⊕" <+> r

cPrintDependent :: (Doc -> Doc -> Doc -> Doc) -> CTerm -> CTerm -> Printer Doc
cPrintDependent fmt l r = do
  left  <- cPrint 0 l
  right <- cPrint 0 r
  return $ asks (fmt . head . fresh) <*> left <*> local bind right

mult, add, var, localVar :: Doc -> Doc
mult = annotate (Term.color Term.Blue <> Term.bold)
add = annotate (Term.color Term.Green <> Term.bold)
var = annotate Term.bold
localVar = annotate (Term.color Term.Yellow <> Term.bold)

