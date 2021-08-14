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
import           Data.Tuple                     ( swap )
import           Data.Void                      ( Void )
import           Text.Megaparsec         hiding ( State )
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer    as L

import           Control.Monad                  ( foldM
                                                , liftM2
                                                , void
                                                )
import           Control.Monad.Reader           ( MonadReader(local)
                                                , Reader
                                                , asks
                                                , runReader
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

identifier :: Parser String
identifier = try $ do
  o <- getOffset
  i <- lexeme $ (:) <$> start <*> rest
  if i `elem` keywords
    then region (setErrorOffset o) (fail $ "unexpected keyword '" <> i <> "'")
    else return i
 where
  start = satisfy (\c -> notElem @[] c "λₘω𝘜" && isAlpha c) <|> char '_'
  rest  = hidden $ many (alphaNumChar <|> oneOf @[] "_'")

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
    try (Let <$> (keyword "let" *> semiring) <*> identifier <* symbol "=")
      <*> iTerm
  assume = Assume <$> (keyword "assume" *> some bind)

eval :: (ZeroOneMany -> ITerm -> a) -> Parser a
eval f = f <$> semiring <*> iTerm

semiring :: Parser ZeroOneMany
semiring = option Many $ choice
  [Zero <$ symbol "0", One <$ symbol "1", Many <$ (keyword "ω" <|> keyword "w")]

iTerm :: Parser ITerm
iTerm = try (cTermInner >>= ann) <|> do
  t <- iTermInner
  ann (Inf t) <|> return t
  where ann t = Ann t <$> (symbol ":" *> cTerm) <?> "type annotation"

iTermInner :: Parser ITerm
iTermInner = foldl (:$:) <$> inner <*> many (cTermWith inner)
 where
  inner =
    choice [letElim, fstElim, sndElim, sumElim, var, parens iTerm]
      <?> "synthesising term"
  letElim = do
    (q, z) <- try $ (,) <$> (keyword "let" *> semiring) <*> identifier <* symbol
      "@"
    let rest elim inLocal tyLocal =
          elim
            <$> (symbol "=" *> iTerm)
            <*> (keyword "in" *> local (inLocal ++) (cTermWith iTermInner))
            <*> (symbol ":" *> local (tyLocal ++) (cTermWith iTermInner))
    (try mUnit *> rest (MUnitElim q) [] [z]) <|> do
      (x, y) <- parens $ (,) <$> identifier <* symbol "," <*> identifier
      rest (MPairElim q) [y, x] [z]
  fstElim = Fst <$> (keyword "fst" *> inner)
  sndElim = Snd <$> (keyword "snd" *> inner)
  sumElim = do
    s <- keyword "case" *> semiring
    z <- identifier <* symbol "@"
    m <- iTerm <* keyword "of"
    let branch side = do
          keyword side
          x <- identifier <* (symbol "→" <|> symbol "->")
          local (x :) (cTermWith iTermInner)
    (l, r) <- braces
      (   ((,) <$> branch "inl" <* symbol ";" <*> branch "inr")
      <|> ((swap .) . (,) <$> branch "inr" <* symbol ";" <*> branch "inl")
      )
    SumElim s m l r <$> (symbol ":" *> local (z :) (cTermWith iTermInner))
  var =
    asks (\r x -> maybe (Free $ Global x) Bound $ elemIndex x r) <*> identifier

cTermWith :: Parser ITerm -> Parser CTerm
cTermWith ip = cTermInner <|> Inf <$> ip

cTerm :: Parser CTerm
cTerm = cTermWith iTerm

cTermInner :: Parser CTerm
cTermInner =
  choice
      (  atomic
      ++ [ lam
         , pi
         , forall
         , try mPair
         , mPairType
         , aPairType
         , sumL
         , sumR
         , sumType
         , try . parens $ cTerm
         ]
      )
    <?> "checkable term"
 where
  atomic = [universe, mUnit, mUnitType, aUnit, aUnitType, aPair]
  lam    = do
    symbol "\\" <|> symbol "λ"
    xs <- some identifier
    symbol "."
    t <- local (reverse xs ++) $ cTermWith iTermInner
    return $ iterate Lam t !! length xs
  universe = Universe <$ (keyword "𝘜" <|> keyword "U")
  pi       = do
    J.Binding x q t <- try $ bind <* (symbol "→" <|> symbol "->")
    Pi q t <$> local (x :) (cTermWith iTermInner)
  forall = do
    keyword "forall" <|> symbol "∀"
    let go bs = do
          b <- bind
          local (bndName b :) (go $ b : bs) <|> return (b : bs)
    xs <- go []
    symbol "."
    p <- local (map bndName xs ++) cTerm
    foldM (\a x -> return $ Pi (bndUsage x) (bndType x) a) p xs
  mPair     = parens $ MPair <$> cTerm <* symbol "," <*> cTerm
  mPairType = do
    J.Binding x q t <- try $ bind <* (symbol "⊗" <|> symbol "*")
    MPairType q t <$> local (x :) (cTermWith iTermInner)
  mUnitType = MUnitType <$ (keyword "𝟭ₘ" <|> keyword "I")
  aPair     = liftM2 (<|>)
                     (between (symbol "⟨") (symbol "⟩"))
                     (between (symbol "<") (symbol ">"))
                     (APair <$> cTerm <* symbol "," <*> cTerm)
  aPairType = do
    (x, t) <-
      try $ parens ((,) <$> identifier <* symbol ":" <*> cTerm) <* symbol "&"
    APairType t <$> local (x :) (cTermWith iTermInner)
  aUnit     = AUnit <$ (symbol "⟨⟩" <|> symbol "<>")
  aUnitType = AUnitType <$ (symbol "⊤" <|> keyword "T")
  sumL      = SumL <$> (keyword "inl" *> cTermWith iTermInner)
  sumR      = SumR <$> (keyword "inr" *> cTermWith iTermInner)
  sumType =
    try
        (   SumType
        <$> choice (atomic ++ [try $ parens cTerm, Inf <$> iTermInner])
        <*  (symbol "⊕" <|> symbol "+")
        )
      <*> cTermWith iTermInner

mUnit :: Parser CTerm
mUnit = MUnit <$ symbol "()"

bind :: Parser Binding
bind =
  parens $ flip J.Binding <$> semiring <*> identifier <* symbol ":" <*> cTerm

