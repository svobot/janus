module Parser
  ( Binding
  , Stmt(..)
  , evalParser
  , fileParser
  , keywords
  , typeParser
  ) where

import           Control.Monad                  ( foldM )
import           Data.Char                      ( isAlpha )
import           Data.List                      ( elemIndex )
import           Prelude                 hiding ( pi )
import           Rig                            ( ZeroOneMany(..) )
import           Text.Parsec
import           Text.Parsec.Language           ( haskellStyle )
import           Text.Parsec.String             ( GenParser )
import qualified Text.Parsec.Token             as P
import           Types                   hiding ( Binding )
import qualified Types                         as T
                                                ( Binding(..) )

type Binding = T.Binding String ZeroOneMany CTerm

data Stmt
  = Let ZeroOneMany String ITerm --  let x = t
  | Assume [Binding]             --  assume x :: t, assume x :: *
  | Eval ZeroOneMany ITerm
  | PutStrLn String --  lhs2TeX hacking, allow to print "magic" string
  | Out String      --  more lhs2TeX hacking, allow to print to files
  deriving (Show, Eq)

lang :: P.TokenParser u
lang = P.makeTokenParser $ haskellStyle
  { P.identStart = satisfy (\c -> notElem @[] c "λ∀" && isAlpha c) <|> char '_'
  , P.reservedNames = keywords ++ ["<>", "()"]
  , P.reservedOpNames = "->" : map pure ":=\\λ.*&@∀,"
  }

keywords :: [String]
keywords = words "forall let assume putStrLn out in U I fst snd T"

evalParser :: String -> Either ParseError Stmt
evalParser = parse (P.whiteSpace lang *> stmt <* eof) "<interactive>"

typeParser :: String -> Either ParseError (ZeroOneMany, ITerm)
typeParser = parse (P.whiteSpace lang *> eval (,) <* eof) "<interactive>"

fileParser :: SourceName -> String -> Either ParseError [Stmt]
fileParser = parse (P.whiteSpace lang *> many stmt <* eof)

type CharParser = GenParser Char ()

identifier :: CharParser String
identifier = P.identifier lang

reserved :: String -> CharParser ()
reserved = P.reserved lang

reservedOp :: String -> CharParser ()
reservedOp = P.reservedOp lang

stmt :: CharParser Stmt
stmt = choice [define, assume, putstr, out, eval Eval]
 where
  define =
    try
        (   Let
        <$> (reserved "let" *> option Many rig)
        <*> (identifier <* reserved "=")
        )
      <*> iTerm []
  assume = Assume . reverse <$> (reserved "assume" *> bindings False [])
  putstr = PutStrLn <$> (reserved "putStrLn" *> P.stringLiteral lang)
  out    = Out <$> (reserved "out" *> option "" (P.stringLiteral lang))

eval :: (ZeroOneMany -> ITerm -> a) -> CharParser a
eval f = f <$> option Many rig <*> iTerm []

rig :: CharParser ZeroOneMany
rig = choice [Zero <$ reserved "0", One <$ reserved "1", Many <$ reserved "w"]

iTerm :: [String] -> CharParser ITerm
iTerm e = (cTermInner e >>= ann) <|> do
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
        rest PairElim ([y, x] ++ e) (z : e)
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
  , try pair
  , tensor
  , mUnit
  , mUnitType
  , try angles
  , with
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
  universe = Universe <$ reserved "U"
  pi       = do
    T.Binding x q t <- try $ bind e <* reservedOp "->"
    Pi q t <$> cTermWith iTermInner (x : e)
  forall = do
    reserved "forall" <|> reservedOp "∀"
    xs <- bindings True e
    reservedOp "."
    p <- cTerm (map bndName xs ++ e)
    foldM (\a x -> return $ Pi (bndUsage x) (bndType x) a) p xs
  pair   = P.parens lang $ Pair <$> cTerm e <* reservedOp "," <*> cTerm e
  tensor = do
    T.Binding x q t <- try $ bind e <* reservedOp "*"
    Tensor q t <$> cTermWith iTermInner (x : e)
  mUnitType = MUnitType <$ reserved "I"
  angles    = P.angles lang $ Angles <$> cTerm e <* reservedOp "," <*> cTerm e
  with      = do
    (x, t) <-
      try
      $  P.parens lang ((,) <$> identifier <* reservedOp ":" <*> cTerm e)
      <* reservedOp "&"
    With t <$> cTermWith iTermInner (x : e)
  aUnit     = AUnit <$ reserved "<>"
  aUnitType = AUnitType <$ reserved "T"

mUnit :: CharParser CTerm
mUnit = MUnit <$ reserved "()"

bind :: [String] -> CharParser Binding
bind e =
  P.parens lang
    $   flip T.Binding
    <$> option Many rig
    <*> identifier
    <*  reservedOp ":"
    <*> cTerm e

bindings :: Bool -> [String] -> CharParser [Binding]
bindings bound = fmap snd . flip go [] where
  go :: [String] -> [Binding] -> CharParser ([String], [Binding])
  go env bs = do
    b <- bind $ if bound then env else []
    go (bndName b : env) (b : bs) <|> return (bndName b : env, b : bs)

