-- | Parser for the Janus language.
module Janus.Parsing
  ( Binding
  , Stmt(..)
  , evalParser
  , fileParser
  , keywords
  , typeParser
  ) where

import           Control.Monad                  ( foldM
                                                , liftM2
                                                )
import           Data.Char                      ( isAlpha )
import           Data.List                      ( elemIndex )
import qualified Janus.Judgment                as J
                                                ( Binding(..) )
import           Janus.Judgment          hiding ( Binding )
import           Janus.Semiring                 ( ZeroOneMany(..) )
import           Janus.Syntax
import           Prelude                 hiding ( pi )
import           Text.Parsec
import           Text.Parsec.Language           ( haskellStyle )
import           Text.Parsec.String             ( GenParser )
import qualified Text.Parsec.Token             as P

type Binding = J.Binding String ZeroOneMany CTerm

-- | Statement in the Janus language.
data Stmt
  = Let ZeroOneMany String ITerm
  | Assume [Binding]
  | Eval ZeroOneMany ITerm
  deriving (Show, Eq)

-- | Language definition derived from the Haskell syntax.
lang :: P.TokenParser u
lang = P.makeTokenParser $ haskellStyle
  { P.identStart      = satisfy (\c -> notElem @[] c "λₘω𝘜" && isAlpha c)
                          <|> char '_'
  , P.reservedNames   = keywords ++ ["<>", "()", "ω", "𝘜", "𝟭ₘ", "⊤"]
  , P.reservedOpNames = "->" : map pure ":=\\λ.*&@∀,→⊗⟨⟩"
  }

-- | Reserved language keywords.
keywords :: [String]
keywords = words "assume forall let in U I fst snd T"

-- | Parse a statement.
evalParser :: String -> Either ParseError Stmt
evalParser = parse (P.whiteSpace lang *> stmt <* eof) "<interactive>"

-- | Parse a Janus expression.
typeParser :: String -> Either ParseError (ZeroOneMany, ITerm)
typeParser = parse (P.whiteSpace lang *> eval (,) <* eof) "<interactive>"

-- | Parse multiple consecutive statements.
fileParser :: SourceName -> String -> Either ParseError [Stmt]
fileParser = parse (P.whiteSpace lang *> many stmt <* eof)

type CharParser = GenParser Char ()

identifier :: CharParser String
identifier = P.identifier lang

reserved, reservedOp :: String -> CharParser ()
reserved = P.reserved lang
reservedOp = P.reservedOp lang

-- | Generate a parser of a single statement.
stmt :: CharParser Stmt
stmt = choice [define, assume, eval Eval]
 where
  define =
    try (Let <$> (reserved "let" *> semiring) <*> identifier <* reserved "=")
      <*> iTerm []
  assume = Assume . reverse <$> (reserved "assume" *> bindings False [])

eval :: (ZeroOneMany -> ITerm -> a) -> CharParser a
eval f = f <$> semiring <*> iTerm []

semiring :: CharParser ZeroOneMany
semiring = option Many $ choice
  [ Zero <$ reserved "0"
  , One <$ reserved "1"
  , Many <$ (reserved "ω" <|> reserved "w")
  ]

iTerm :: [String] -> CharParser ITerm
iTerm e = try (cTermInner e >>= ann) <|> do
  t <- iTermInner e
  ann (Inf t) <|> return t
  where ann t = Ann t <$> (reservedOp ":" *> cTerm e)

iTermInner :: [String] -> CharParser ITerm
iTermInner e = foldl (:$:) <$> inner e <*> many (cTermWith inner e)
 where
  inner e' = choice [letElim, fstElim, sndElim, var, P.parens lang $ iTerm e']
  letElim = do
    z <- try $ reserved "let" *> identifier <* reserved "@"
    let rest elim ine tye =
          elim
            <$> (reservedOp "=" *> iTerm e)
            <*> (reserved "in" *> cTermWith iTermInner ine)
            <*> (reservedOp ":" *> cTermWith iTermInner tye)
    (do
        x <- identifier
        y <- reservedOp "," *> identifier
        rest MPairElim ([y, x] ++ e) (z : e)
      )
      <|> (mUnit *> rest MUnitElim e (z : e))
  fstElim = Fst <$> (reserved "fst" *> inner e)
  sndElim = Snd <$> (reserved "snd" *> inner e)
  var     = (\x -> maybe (Free $ Global x) Bound $ elemIndex x e) <$> identifier

cTermWith :: ([String] -> CharParser ITerm) -> [String] -> CharParser CTerm
cTermWith ip e = cTermInner e <|> Inf <$> ip e

cTerm :: [String] -> CharParser CTerm
cTerm = cTermWith iTerm

cTermInner :: [String] -> CharParser CTerm
cTermInner e = choice
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
  , try . P.parens lang $ cTerm e
  ]
 where
  lam = do
    reservedOp "\\" <|> reservedOp "λ"
    xs <- many1 identifier
    reservedOp "."
    t <- cTermWith iTermInner (reverse xs ++ e)
    return $ iterate Lam t !! length xs
  universe = Universe <$ (reserved "𝘜" <|> reserved "U")
  pi       = do
    J.Binding x q t <- try $ bind e <* (reservedOp "→" <|> reservedOp "->")
    Pi q t <$> cTermWith iTermInner (x : e)
  forall = do
    reserved "forall" <|> reservedOp "∀"
    xs <- bindings True e
    reservedOp "."
    p <- cTerm (map bndName xs ++ e)
    foldM (\a x -> return $ Pi (bndUsage x) (bndType x) a) p xs
  mPair     = P.parens lang $ MPair <$> cTerm e <* reservedOp "," <*> cTerm e
  mPairType = do
    J.Binding x q t <- try $ bind e <* (reservedOp "⊗" <|> reservedOp "*")
    MPairType q t <$> cTermWith iTermInner (x : e)
  mUnitType = MUnitType <$ (reserved "𝟭ₘ" <|> reserved "I")
  aPair =
    liftM2 (<|>) (between (reservedOp "⟨") (reservedOp "⟩")) (P.angles lang)
      $   APair
      <$> cTerm e
      <*  reservedOp ","
      <*> cTerm e
  aPairType = do
    (x, t) <-
      try
      $  P.parens lang ((,) <$> identifier <* reservedOp ":" <*> cTerm e)
      <* reservedOp "&"
    APairType t <$> cTermWith iTermInner (x : e)
  aUnit     = AUnit <$ (reserved "⟨⟩" <|> reserved "<>")
  aUnitType = AUnitType <$ (reserved "⊤" <|> reserved "T")

mUnit :: CharParser CTerm
mUnit = MUnit <$ reserved "()"

bind :: [String] -> CharParser Binding
bind e =
  P.parens lang
    $   flip J.Binding
    <$> semiring
    <*> identifier
    <*  reservedOp ":"
    <*> cTerm e

-- | Parse multiple consecutive variable bindings.
bindings :: Bool -> [String] -> CharParser [Binding]
bindings bound = fmap snd . flip go [] where
  go :: [String] -> [Binding] -> CharParser ([String], [Binding])
  go env bs = do
    b <- bind $ if bound then env else []
    go (bndName b : env) (b : bs) <|> return (bndName b : env, b : bs)

