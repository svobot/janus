{-# OPTIONS_GHC -fno-warn-missed-specialisations #-}

-- | Parser for the Janus language.
module Janus.Parsing
  ( Binding
  , Stmt(..)
  , evalParser
  , fileParser
  , keywords
  , typeParser
  ) where

import           Control.Applicative     hiding ( many
                                                , some
                                                )
import           Data.Bifunctor                 ( second )
import           Data.Tuple                     ( swap )
import           Data.Void                      ( Void )
import           Text.Megaparsec         hiding ( State )
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer    as L

import           Control.Monad                  ( foldM
                                                , liftM2
                                                , void
                                                , when
                                                )
import           Control.Monad.Reader           ( MonadReader(local)
                                                , Reader
                                                , ask
                                                , runReader
                                                )
import           Data.Char                      ( isAlpha )
import           Data.List                      ( elemIndices
                                                , foldl'
                                                )
import           Data.Maybe                     ( fromMaybe )
import           Janus.Judgment                 ( Binding(..) )
import           Janus.Semiring                 ( ZeroOneMany(..) )
import           Janus.Syntax
import           Prelude                 hiding ( pi )

type ParsedBinding = Binding String ZeroOneMany CTerm

-- | Statement in the Janus language.
data Stmt
  = Let ZeroOneMany String ITerm
  | Assume [ParsedBinding]
  | Eval ZeroOneMany ITerm
  deriving (Show, Eq)

type Parser = ParsecT Void String (Reader [String])

ws :: Parser ()
ws =
  L.space space1 (L.skipLineComment "--") (L.skipBlockCommentNested "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme ws

symbol :: String -> Parser ()
symbol = void . L.symbol ws

keyword :: String -> Parser ()
keyword k = void $ lexeme (string k <* notFollowedBy alphaNumChar)

identifier :: Bool -> Parser (String, Maybe Int)
identifier withIndex = try $ do
  o       <- getOffset
  (n, mi) <- lexeme $ (,) <$> ((:) <$> start <*> rest) <*> option
    Nothing
    (Just <$> (char '#' *> L.decimal))
  when (n `elem` keywords)
    $ region (setErrorOffset o) (fail $ "unexpected keyword '" <> n <> "'")
  case mi of
    Just i | not withIndex -> region
      (setErrorOffset o)
      (fail $ "unexpected variable index '#" <> show i <> "'")
    _ -> return (n, mi)
 where
  start = satisfy (\c -> notElem @[] c "λₘω𝘜" && isAlpha c) <|> char '_'
  rest  = hidden $ many (alphaNumChar <|> oneOf @[] "_'")

name :: Parser String
name = fst <$> identifier False

parens, braces :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")
braces = between (symbol "{") (symbol "}")

-- | Reserved language keywords.
keywords :: [String]
keywords = words "assume forall let in U I fst snd T inl inr case of"

-- | Parse a statement.
evalParser :: String -> Either (ParseErrorBundle String Void) Stmt
evalParser = flip runReader [] . runParserT (ws *> stmt <* eof) "<interactive>"

-- | Parse a Janus expression.
typeParser
  :: String -> Either (ParseErrorBundle String Void) (ZeroOneMany, ITerm)
typeParser =
  flip runReader [] . runParserT (ws *> eval (,) <* eof) "<interactive>"

-- | Parse multiple consecutive statements.
fileParser :: String -> String -> Either (ParseErrorBundle String Void) [Stmt]
fileParser = (flip runReader [] .) . runParserT (ws *> many stmt <* eof)

-- | Generate a parser of a single statement.
stmt :: Parser Stmt
stmt = choice [define, assume, eval Eval]
 where
  define =
    try (Let <$> (keyword "let" *> semiring) <*> name <* symbol "=") <*> iTerm
  assume = Assume <$> (keyword "assume" *> some bind)

eval :: (ZeroOneMany -> ITerm -> a) -> Parser a
eval f = f <$> semiring <*> iTerm

semiring :: Parser ZeroOneMany
semiring = option Many $ choice
  [Zero <$ symbol "0", One <$ symbol "1", Many <$ (keyword "ω" <|> keyword "w")]

annotation :: Parser CTerm
annotation =
  symbol ":"
    *>  choice
          [ cTermInner False >>= \case
            Inf i -> Inf <$> application i
            c     -> pure c
          , Inf <$> iTermInner
          ]
    <?> "type annotation"

application :: ITerm -> Parser ITerm
application t = foldl' (:$:) t <$> many (cTermWith True $ var <|> parens iTerm)

var :: Parser ITerm
var = do
  o      <- getOffset
  names  <- ask
  (n, i) <- second (fromMaybe 0) <$> identifier True
  case elemIndices n names of
    []                 -> return . Free $ Global n
    ns | i < length ns -> return . Bound $ ns !! i
    ns                 -> region
      (setErrorOffset o)
      (fail $ "index of the bound variable is too large\n" <> mconcat
        ["only ", show (length ns), " variables '", n, "' are in context"]
      )

iTerm :: Parser ITerm
iTerm = try (cTermInner False >>= (\t -> Ann t <$> annotation)) <|> do
  t <- iTermInner
  Ann (Inf t) <$> annotation <|> return t

iTermInner :: Parser ITerm
iTermInner =
  choice
      [var <|> parens iTerm >>= application, letElim, fstElim, sndElim, sumElim]
    <?> "synthesising term"
 where
  oneOrMany = option Many
    $ choice [One <$ symbol "1", Many <$ (keyword "ω" <|> keyword "w")]
  letElim = do
    (q, z) <- try $ (,) <$> (keyword "let" *> semiring) <*> name <* symbol "@"
    let rest elim inLocals tyLocals =
          elim
            <$> (symbol "=" *> iTerm <* keyword "in")
            <*> local (inLocals <>) (cTermWith False iTermInner)
            <*> local (tyLocals <>) annotation
    (try mUnit *> rest (MUnitElim q z) [] [z]) <|> do
      (x, y) <- parens $ (,) <$> name <* symbol "," <*> name
      rest (MPairElim q z x y) [y, x] [z]
  fstElim = Fst <$> (keyword "fst" *> (var <|> parens iTerm))
  sndElim = Snd <$> (keyword "snd" *> (var <|> parens iTerm))
  sumElim = do
    s <- keyword "case" *> oneOrMany
    z <- name <* symbol "@"
    m <- iTerm <* keyword "of"
    let branch side = do
          keyword side
          x <- name <* (symbol "→" <|> symbol "->")
          (x, ) <$> local (x :) (cTermWith False iTermInner)
    ((x, l), (y, r)) <- braces
      (   ((,) <$> branch "inl" <* symbol ";" <*> branch "inr")
      <|> ((swap .) . (,) <$> branch "inr" <* symbol ";" <*> branch "inl")
      )
    SumElim s z m x l y r <$> local (z :) annotation

cTermWith :: Bool -> Parser ITerm -> Parser CTerm
cTermWith atomicOnly iTermP = try (cTermInner atomicOnly) <|> Inf <$> iTermP

cTerm :: Parser CTerm
cTerm = do
  c <- cTermWith False iTermInner
  (Inf . Ann c <$> annotation) <|> pure c

cTermInner :: Bool -> Parser CTerm
cTermInner atomicOnly =
  choice
      (  (if atomicOnly
           then []
           else [lam, pi, forall_, mPairType, aPairType, sumL, sumR, sumType]
         )
      <> [universe, mUnit, mUnitType, aUnit, aUnitType, aPair, mPairOrParens]
      )
    <?> "checkable term"
 where
  lam = do
    xs <- (symbol "\\" <|> symbol "λ") *> some name <* symbol "."
    t  <- local (reverse xs <>) $ cTermWith False iTermInner
    return $ foldr Lam t xs
  universe = Universe <$ (keyword "𝘜" <|> keyword "U")
  pi       = do
    Binding x q t <- try $ bind <* (symbol "→" <|> symbol "->")
    Pi q x t <$> local (x :) (cTermWith False iTermInner)
  forall_ = do
    keyword "forall" <|> symbol "∀"
    let go bs = do
          b <- bind
          local (bndName b :) (go $ b : bs) <|> return (b : bs)
    xs <- go [] <* symbol "."
    p  <- local (map bndName xs <>) cTerm
    foldM (\a x -> return $ Pi (bndUsage x) (bndName x) (bndType x) a) p xs
  mPairType = do
    Binding x q t <- try $ bind <* (symbol "⊗" <|> symbol "*")
    MPairType q x t <$> local (x :) (cTermWith True iTermInner)
  mUnitType = MUnitType <$ (keyword "𝟭ₘ" <|> keyword "I")
  aPair     = liftM2 (<|>)
                     (between (symbol "⟨") (symbol "⟩"))
                     (between (symbol "<") (symbol ">"))
                     (APair <$> cTerm <* symbol "," <*> cTerm)
  aPairType = do
    (x, t) <- try $ parens ((,) <$> name <* symbol ":" <*> cTerm) <* symbol "&"
    APairType x t <$> local (x :) (cTermWith True iTermInner)
  aUnit     = AUnit <$ (symbol "⟨⟩" <|> symbol "<>")
  aUnitType = AUnitType <$ (symbol "⊤" <|> keyword "T")
  sumL      = SumL <$> (keyword "inl" *> cTermWith True iTermInner)
  sumR      = SumR <$> (keyword "inr" *> cTermWith True iTermInner)
  sumType =
    try (SumType <$> cTermWith True iTermInner <* (symbol "⊕" <|> symbol "+"))
      <*> cTermWith True iTermInner
  mPairOrParens = parens $ do
    t <- cTerm
    (MPair t <$> (symbol "," *> cTerm)) <|> pure t

mUnit :: Parser CTerm
mUnit = MUnit <$ symbol "()"

bind :: Parser ParsedBinding
bind = parens $ flip Binding <$> semiring <*> name <* symbol ":" <*> cTerm

