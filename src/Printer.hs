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

import           Control.Monad.Reader           ( MonadReader(local)
                                                , Reader
                                                , asks
                                                , runReader
                                                )
import           Control.Monad.State            ( State
                                                , modify
                                                , runState
                                                )
import           Data.List                      ( intersperse )
import qualified Data.Set                      as Set
import           Data.Text                      ( Text )
import           Data.Text.Prettyprint.Doc
import           Data.Text.Prettyprint.Doc.Render.String
                                                ( renderString )
import qualified Data.Text.Prettyprint.Doc.Render.Terminal
                                               as Term
import           Rig                            ( ZeroOneMany(..) )
import           Types

type TermDoc = Doc Term.AnsiStyle

instance Pretty Name where
  pretty (Global s) = pretty s
  pretty x          = "[" <> pretty (show x) <> "]"

class PrettyAnsi a where
  prettyAnsi :: a -> TermDoc

instance PrettyAnsi Text where
  prettyAnsi = pretty

instance PrettyAnsi ITerm where
  prettyAnsi = runPrinter $ iPrint 0

instance PrettyAnsi CTerm where
  prettyAnsi = runPrinter $ cPrint 0

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

render :: TermDoc -> Text
render = Term.renderStrict . layoutSmart defaultLayoutOptions

renderErr :: TermDoc -> Text
renderErr =
  Term.renderStrict
    . layoutSmart defaultLayoutOptions
    . (annotate (Term.color Term.Red <> Term.bold) "error:" <+>)
    . align

hardlines :: [Doc ann] -> Doc ann
hardlines = mconcat . intersperse hardline

renderBinding :: Maybe String -> Binding Value ZeroOneMany Type -> TermDoc
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

parensIf :: Bool -> Doc ann -> Doc ann
parensIf True  = parens
parensIf False = id

type Printer doc = State FreeVars (Reader (NameEnv doc) doc)
type FreeVars = Set.Set String
data NameEnv doc = NameEnv
  { fresh :: [doc]
  , bound :: [doc]
  }

runPrinter :: (a -> Printer (Doc ann)) -> a -> Doc ann
runPrinter printer term = runReader r (NameEnv (freshNames finalState) [])
 where
  (r, finalState) = runState (printer term) Set.empty
  -- Filter the free variables that occur in the term out of the names that can
  -- be used for bound variables.
  freshNames freeVars =
    [ pretty $ c : n
    | n <- "" : map show [1 :: Int ..]
    , c <- ['x', 'y', 'z'] ++ ['a' .. 'w']
    , (c : n) `Set.notMember` freeVars
    ]

skip :: Int -> NameEnv a -> NameEnv a
skip i env = env { fresh = drop i $ fresh env }

bind :: NameEnv a -> NameEnv a
bind (NameEnv (new : fs) bs) = NameEnv fs (new : bs)
bind _                       = error "internal: No new variable name available."

bindMany :: Int -> NameEnv a -> NameEnv a
bindMany n (NameEnv as bs) = NameEnv (drop n as) (reverse (take n as) ++ bs)

iPrint :: Int -> ITerm -> Printer TermDoc
iPrint p (Ann c c') = (<*>) . (fmt <$>) <$> cPrint 2 c <*> cPrint 0 c'
  where fmt val ty = parensIf (p > 1) $ val <+> ":" <+> ty
iPrint _ (Bound k) = return . asks $ (!! k) . bound
iPrint _ (Free  n) = do
  case n of
    Global s -> modify (Set.insert s)
    _        -> return ()
  return . return $ pretty n
iPrint p (i :$: c) = (<*>) . (fmt <$>) <$> iPrint 2 i <*> cPrint 3 c
  where fmt f x = parensIf (p > 2) . align $ sep [f, x]
iPrint p (PairElim l i t) = do
  letPart  <- iPrint 0 l
  inPart   <- cPrint 0 i
  typePart <- cPrint 0 t
  return
    $   asks fmt
    <*> letPart
    <*> local (bindMany 2)    inPart
    <*> local (bind . skip 2) typePart
 where
  fmt (NameEnv ns _) letPart inPart typePart = parensIf (p > 0) . align $ sep
    [ multAnn "let"
    <+> varAnn (ns !! 2)
    <+> multAnn "@"
    <+> varAnn (head ns)
    <>  multAnn ","
    <+> varAnn (ns !! 1)
    <+> multAnn "="
    <+> letPart
    , multAnn "in" <+> inPart <+> multAnn ":" <+> typePart
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
    [ multAnn "let"
    <+> varAnn name
    <+> multAnn "@"
    <+> multAnn "()"
    <+> multAnn "="
    <+> letPart
    , multAnn "in" <+> inPart <+> multAnn ":" <+> typePart
    ]
iPrint p (Fst i) = (parensIf (p > 0) . (addAnn "fst" <+>) <$>) <$> iPrint 3 i
iPrint p (Snd i) = (parensIf (p > 0) . (addAnn "snd" <+>) <$>) <$> iPrint 3 i

cPrint :: Int -> CTerm -> Printer TermDoc
cPrint p (Inf i) = iPrint p i
cPrint p (Lam c) = (parensIf (p > 0) <$>) <$> go 0 c
 where
  go depth (Lam c') = go (depth + 1) c'
  go depth c'       = do
    body <- cPrint 0 c'
    return $ asks (fmt depth) <*> local (bindMany $ depth + 1) body
  fmt depth (NameEnv ns _) body = do
    "λ" <> hsep (map (varAnn . (ns !!)) [0 .. depth]) <> "." <+> body
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
      return . align $ sep ["∀" <+> align (sep bindsDoc) <+> ".", bodyDoc]
  fmtBind q name body = parens $ prettyAnsi q <+> varAnn name <+> ":" <+> body
cPrint p (Pi q c c') = cPrintDependent fmt c c'
 where
  fmt name l r = parensIf (p > 0) $ sep
    ["(" <> prettyAnsi q <+> varAnn name <+> ":" <+> l <> ")" <+> "->", r]
cPrint p (Tensor q c c') = cPrintDependent fmt c c'
 where
  fmt name l r = do
    parensIf (p > 0) $ sep
      [ multAnn "("
      <>  prettyAnsi q
      <+> varAnn name
      <+> ":"
      <+> l
      <>  multAnn ")"
      <+> multAnn "*"
      , r
      ]
cPrint p (With c c') = cPrintDependent fmt c c'
 where
  fmt name l r = parensIf (p > 0) $ sep
    [addAnn "(" <> varAnn name <+> ":" <+> l <> addAnn ")" <+> addAnn "&", r]
cPrint _ (Pair c c') = (<*>) . (fmt <$>) <$> cPrint 0 c <*> cPrint 0 c'
  where fmt l r = multAnn "(" <> l <> multAnn "," <+> r <> multAnn ")"
cPrint _ (Angles c c') = (<*>) . (fmt <$>) <$> cPrint 0 c <*> cPrint 0 c'
  where fmt l r = addAnn "<" <> l <> addAnn "," <+> r <> addAnn ">"
cPrint _ Universe  = return . return $ "U"
cPrint _ MUnit     = return . return $ multAnn "()"
cPrint _ MUnitType = return . return $ multAnn "I"
cPrint _ AUnit     = return . return $ addAnn "<>"
cPrint _ AUnitType = return . return $ addAnn "T"

cPrintDependent
  :: (TermDoc -> TermDoc -> TermDoc -> TermDoc)
  -> CTerm
  -> CTerm
  -> Printer TermDoc
cPrintDependent fmt l r = do
  left  <- cPrint 0 l
  right <- cPrint 0 r
  return $ asks (fmt . head . fresh) <*> left <*> local bind right

multAnn :: TermDoc -> TermDoc
multAnn = annotate (Term.color Term.Blue <> Term.bold)

addAnn :: TermDoc -> TermDoc
addAnn = annotate (Term.color Term.Green <> Term.bold)

varAnn :: TermDoc -> TermDoc
varAnn = annotate Term.bold

