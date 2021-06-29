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
import           Data.Void                      ( Void )
import           Text.Megaparsec         hiding ( State )
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer    as L

import           Control.Monad                  ( foldM
                                                , liftM2
                                                , void
                                                )
import           Data.Char                      ( isAlpha )
import           Data.List                      ( elemIndex )
import qualified Janus.Judgment                as J
                                                ( Binding(..) )
import           Janus.Judgment          hiding ( Binding )
import           Janus.Semiring                 ( ZeroOneMany(..) )
import           Janus.Syntax
import           Prelude                 hiding ( pi )

type Binding = J.Binding String ZeroOneMany CTerm

-- | Statement in the Janus language.
data Stmt
  = Let ZeroOneMany String ITerm
  | Assume [Binding]
  | Eval ZeroOneMany ITerm
  deriving (Show, Eq)

type Parser = Parsec Void String

ws :: Parser ()
ws =
  L.space space1 (L.skipLineComment "--") (L.skipBlockCommentNested "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme ws

symbol :: String -> Parser ()
symbol = void . L.symbol ws

keyword :: String -> Parser ()
keyword k = void $ lexeme (string k <* notFollowedBy alphaNumChar)

identifier :: Parser String
identifier = try $ do
  ident <- lexeme $ (:) <$> start <*> rest
  if ident `elem` keywords then fail $ "keyword " ++ ident else return ident
 where
  start = satisfy (\c -> notElem @[] c "λₘω𝘜" && isAlpha c) <|> char '_'
  rest  = hidden $ many (alphaNumChar <|> oneOf @[] "_'")

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

-- | Reserved language keywords.
keywords :: [String]
keywords = words "assume forall let in U I fst snd T"

-- | Parse a statement.
evalParser :: String -> Either (ParseErrorBundle String Void) Stmt
evalParser = parse (ws *> stmt <* eof) "<interactive>"

-- | Parse a Janus expression.
typeParser
  :: String -> Either (ParseErrorBundle String Void) (ZeroOneMany, ITerm)
typeParser = parse (ws *> eval (,) <* eof) "<interactive>"

-- | Parse multiple consecutive statements.
fileParser :: String -> String -> Either (ParseErrorBundle String Void) [Stmt]
fileParser = parse (ws *> many stmt <* eof)

-- | Generate a parser of a single statement.
stmt :: Parser Stmt
stmt = choice [define, assume, eval Eval]
 where
  define =
    try (Let <$> (keyword "let" *> semiring) <*> identifier <* symbol "=")
      <*> iTerm []
  assume = Assume . reverse <$> (keyword "assume" *> bindings False [])

eval :: (ZeroOneMany -> ITerm -> a) -> Parser a
eval f = f <$> semiring <*> iTerm []

semiring :: Parser ZeroOneMany
semiring = option Many $ choice
  [Zero <$ symbol "0", One <$ symbol "1", Many <$ (symbol "ω" <|> symbol "w")]

iTerm :: [String] -> Parser ITerm
iTerm e = try (cTermInner e >>= ann) <|> do
  t <- iTermInner e
  ann (Inf t) <|> return t
  where ann t = Ann t <$> (symbol ":" *> cTerm e) <?> "type annotation"

iTermInner :: [String] -> Parser ITerm
iTermInner e = foldl (:$:) <$> inner e <*> many (cTermWith inner e)
 where
  inner e' =
    choice [letElim, fstElim, sndElim, var, parens $ iTerm e']
      <?> "synthesising term"
  letElim = do
    z <- try $ keyword "let" *> identifier <* symbol "@"
    let rest elim ine tye =
          elim
            <$> (symbol "=" *> iTerm e)
            <*> (keyword "in" *> cTermWith iTermInner ine)
            <*> (symbol ":" *> cTermWith iTermInner tye)
    (do
        x <- identifier
        y <- symbol "," *> identifier
        rest MPairElim ([y, x] ++ e) (z : e)
      )
      <|> (mUnit *> rest MUnitElim e (z : e))
  fstElim = Fst <$> (keyword "fst" *> inner e)
  sndElim = Snd <$> (keyword "snd" *> inner e)
  var     = (\x -> maybe (Free $ Global x) Bound $ elemIndex x e) <$> identifier

cTermWith :: ([String] -> Parser ITerm) -> [String] -> Parser CTerm
cTermWith ip e = cTermInner e <|> Inf <$> ip e

cTerm :: [String] -> Parser CTerm
cTerm = cTermWith iTerm

cTermInner :: [String] -> Parser CTerm
cTermInner e =
  choice
      [ lam
      , universe
      , pi
      , forall
      , try mPair
      , mPairType
      , mUnit
      , mUnitType
      , try aPair
      , aPairType
      , aUnit
      , aUnitType
      , try . parens $ cTerm e
      ]
    <?> "checkable term"
 where
  lam = do
    symbol "\\" <|> symbol "λ"
    xs <- some identifier
    symbol "."
    t <- cTermWith iTermInner (reverse xs ++ e)
    return $ iterate Lam t !! length xs
  universe = Universe <$ (keyword "𝘜" <|> keyword "U")
  pi       = do
    J.Binding x q t <- try $ bind e <* (symbol "→" <|> symbol "->")
    Pi q t <$> cTermWith iTermInner (x : e)
  forall = do
    keyword "forall" <|> symbol "∀"
    xs <- bindings True e
    symbol "."
    p <- cTerm (map bndName xs ++ e)
    foldM (\a x -> return $ Pi (bndUsage x) (bndType x) a) p xs
  mPair     = parens $ MPair <$> cTerm e <* symbol "," <*> cTerm e
  mPairType = do
    J.Binding x q t <- try $ bind e <* (symbol "⊗" <|> symbol "*")
    MPairType q t <$> cTermWith iTermInner (x : e)
  mUnitType = MUnitType <$ (keyword "𝟭ₘ" <|> keyword "I")
  aPair =
    liftM2 (<|>)
           (between (symbol "⟨") (symbol "⟩"))
           (between (symbol "<") (symbol ">"))
      $   APair
      <$> cTerm e
      <*  symbol ","
      <*> cTerm e
  aPairType = do
    (x, t) <-
      try $ parens ((,) <$> identifier <* symbol ":" <*> cTerm e) <* symbol "&"
    APairType t <$> cTermWith iTermInner (x : e)
  aUnit     = AUnit <$ (symbol "⟨⟩" <|> symbol "<>")
  aUnitType = AUnitType <$ (symbol "⊤" <|> keyword "T")

mUnit :: Parser CTerm
mUnit = MUnit <$ symbol "()"

bind :: [String] -> Parser Binding
bind e =
  parens $ flip J.Binding <$> semiring <*> identifier <* symbol ":" <*> cTerm e

-- | Parse multiple consecutive variable bindings.
bindings :: Bool -> [String] -> Parser [Binding]
bindings bound = fmap snd . flip go [] where
  go :: [String] -> [Binding] -> Parser ([String], [Binding])
  go env bs = do
    b <- bind $ if bound then env else []
    go (bndName b : env) (b : bs) <|> return (bndName b : env, b : bs)

