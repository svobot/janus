module Parser
  ( Binding
  , Origin(OITerm)
  , Stmt(..)
  , eval
  , file
  , iTerm
  , keywords
  , parseIO
  , stmt
  ) where

import           Control.Monad                  ( foldM )
import           Control.Monad.Trans            ( liftIO )
import           Data.List                      ( elemIndex )
import           Rig                            ( ZeroOneMany(..) )
import           Text.Parsec
import           Text.Parsec.Language           ( haskellStyle )
import           Text.Parsec.String             ( GenParser )
import qualified Text.Parsec.Token             as P
import           Types                   hiding ( Binding )
import qualified Types                         as T
                                                ( Binding(..) )

lambdaPi :: P.TokenParser u
lambdaPi = P.makeTokenParser $ haskellStyle
  { P.identStart      = letter <|> char '_'
  , P.reservedNames   = keywords ++ ["<>", "()"]
  , P.reservedOpNames = [ ":"
                        , "="
                        , "\\"
                        , "λ"
                        , "."
                        , "->"
                        , "*"
                        , "&"
                        , "@"
                        , "∀"
                        , ","
                        ]
  }

keywords :: [String]
keywords =
  [ "forall"
  , "let"
  , "assume"
  , "putStrLn"
  , "out"
  , "in"
  , "U"
  , "MUnit"
  , "Fst"
  , "Snd"
  , "AUnit"
  ]

identifier :: CharParser () String
identifier = P.identifier lambdaPi

reserved :: String -> CharParser st ()
reserved = P.reserved lambdaPi

reservedOp :: String -> CharParser st ()
reservedOp = P.reservedOp lambdaPi

type CharParser st = GenParser Char st
data Origin = OAnn | OApp | OITerm | OCTerm | OStale deriving (Eq)
type Binding = T.Binding String ZeroOneMany CTerm

data Stmt
  = Let ZeroOneMany String ITerm --  let x = t
  | Assume [Binding]             --  assume x :: t, assume x :: *
  | Eval ZeroOneMany ITerm
  | PutStrLn String --  lhs2TeX hacking, allow to print "magic" string
  | Out String      --  more lhs2TeX hacking, allow to print to files
  deriving (Show, Eq)

parseIO :: String -> CharParser () a -> String -> Repl (Maybe a)
parseIO f p x = case parse (P.whiteSpace lambdaPi *> p <* eof) f x of
  Left  e -> liftIO $ print e >> return Nothing
  Right r -> return (Just r)

stmt :: CharParser () Stmt
stmt = choice [define, assume', putstr, out, eval Eval]
 where
  define =
    try
        (   Let
        <$> (reserved "let" *> option Many rig)
        <*> (identifier <* reserved "=")
        )
      <*> iTerm OITerm []
  assume' = Assume . reverse <$> (reserved "assume" *> bindings False [])
  putstr  = PutStrLn <$> (reserved "putStrLn" *> P.stringLiteral lambdaPi)
  out     = Out <$> (reserved "out" *> option "" (P.stringLiteral lambdaPi))

eval :: (ZeroOneMany -> ITerm -> a) -> CharParser () a
eval f = f <$> option Many rig <*> iTerm OITerm []

file :: String -> String -> Repl (Maybe [Stmt])
file name = parseIO name $ many stmt

rig :: CharParser () ZeroOneMany
rig = choice [Zero <$ reserved "0", One <$ reserved "1", Many <$ reserved "w"]

iTerm :: Origin -> [String] -> CharParser () ITerm
iTerm b e =
  choice
    $  [ try ann | b /= OAnn && b /= OApp ]
    ++ [ try $ app e | b /= OApp ]
    ++ [ pairElim
       , mUnitElim
       , fstElim
       , sndElim
       , var
       , P.parens lambdaPi $ iTerm OITerm e
       ]
 where
  ann =
    Ann
      <$> cTerm (if b == OCTerm then OStale else OAnn) e
      <*  reservedOp ":"
      <*> cTerm OAnn e
  pairElim = do
    (z, x, y) <-
      try
      $   (,,)
      <$> (reserved "let" *> identifier)
      <*> (reservedOp "@" *> identifier)
      <*> (reservedOp "," *> identifier)
      <*  reservedOp "="
    m <- iTerm OITerm e
    reserved "in"
    n <- cTerm OCTerm ([y, x] ++ e)
    reservedOp ":"
    t <- cTerm OCTerm (z : e)
    return $ PairElim m n t
  mUnitElim = do
    reserved "let"
    x <- identifier
    MUnitElim
      <$> (reservedOp "@" *> mUnit *> reservedOp "=" *> iTerm OITerm e)
      <*  reserved "in"
      <*> (cTerm OCTerm e <* reservedOp ":")
      <*> cTerm OCTerm (x : e)
  fstElim = Fst <$> (reserved "Fst" *> iTerm OITerm e)
  sndElim = Snd <$> (reserved "Snd" *> iTerm OITerm e)
  var     = (\x -> maybe (Free $ Global x) Bound $ elemIndex x e) <$> identifier

cTerm :: Origin -> [String] -> CharParser () CTerm
cTerm b e =
  choice
    $  [ parseLam e
       , universe
       , fun
       , forall
       , try pair
       , tensor
       , mUnit
       , mUnitType
       , try angles
       , with
       , aUnit
       , aUnitType
       , P.parens lambdaPi $ cTerm OCTerm e
       ]
    ++ [ Inf <$> iTerm b e | b /= OStale ]
 where
  universe = Universe <$ reserved "U"
  fun      = do
    T.Binding e' q t <- try $ bind e <* reservedOp "->"
    p                <- cTerm OCTerm (e' : e)
    return (Pi q t p)
  forall = do
    reserved "forall" <|> reservedOp "∀"
    xs <- bindings True e
    reservedOp "."
    p <- cTerm OCTerm (map bndName xs ++ e)
    foldM (\a x -> return $ Pi (bndUsage x) (bndType x) a) p xs
  pair =
    P.parens lambdaPi
      $   Pair
      <$> cTerm OCTerm e
      <*  reservedOp ","
      <*> cTerm OCTerm e
  tensor = do
    T.Binding e' q t <- try $ bind e <* reservedOp "*"
    p                <- cTerm OCTerm (e' : e)
    return (Tensor q t p)
  mUnitType = MUnitType <$ reserved "MUnit"
  angles =
    P.angles lambdaPi
      $   Angles
      <$> cTerm OCTerm e
      <*  reservedOp ","
      <*> cTerm OCTerm e
  with = do
    (x, t) <-
      try
      $  P.parens lambdaPi
                  ((,) <$> identifier <* reservedOp ":" <*> cTerm OCTerm e)
      <* reservedOp "&"
    p <- cTerm OCTerm (x : e)
    return $ With t p
  aUnit     = AUnit <$ reserved "<>"
  aUnitType = AUnitType <$ reserved "AUnit"

mUnit :: CharParser () CTerm
mUnit = MUnit <$ reserved "()"

parseLam :: [String] -> CharParser () CTerm
parseLam e = do
  reservedOp "\\" <|> reservedOp "λ"
  xs <- many1 identifier
  reservedOp "."
  t <- cTerm OCTerm (reverse xs ++ e)
  return $ iterate Lam t !! length xs

app :: [String] -> CharParser () ITerm
app e = foldl (:$:) <$> iTerm OApp e <*> many1 (cTerm OApp e)

bind :: [String] -> CharParser () Binding
bind e =
  P.parens lambdaPi
    $   flip T.Binding
    <$> option Many rig
    <*> identifier
    <*  reservedOp ":"
    <*> cTerm OCTerm e

bindings :: Bool -> [String] -> CharParser () [Binding]
bindings bound = fmap snd . flip go [] where
  go :: [String] -> [Binding] -> CharParser () ([String], [Binding])
  go env bs = do
    b <- bind $ if bound then env else []
    go (bndName b : env) (b : bs) <|> return (bndName b : env, b : bs)

