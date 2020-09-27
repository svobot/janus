module Parser where

import           Control.Monad.Trans            ( liftIO )
import           Data.List                      ( elemIndex )
import           Data.Maybe                     ( fromMaybe )
import           Text.Parsec
import           Text.Parsec.String             ( GenParser )
import           Text.Parsec.Token
import           Text.Parsec.Language           ( haskellStyle )
import           Types

lambdaPi :: TokenParser u
lambdaPi = makeTokenParser
  (haskellStyle
    { identStart    = letter <|> char '_'
    , reservedNames = [ "forall"
                      , "let"
                      , "assume"
                      , "putStrLn"
                      , "out"
                      , "in"
                      , "Unit"
                      ]
    }
  )

type CharParser st = GenParser Char st
data Origin = OAnn | OApp | OITerm | OCTerm | OStale deriving (Eq)

data Stmt = Let ZeroOneOmega String ITerm               --  let x = t
          | Assume [(ZeroOneOmega, String, CTerm)] --  assume x :: t, assume x :: *
          | Eval ITerm
          | PutStrLn String         --  lhs2TeX hacking, allow to print "magic" string
          | Out String              --  more lhs2TeX hacking, allow to print to files
  deriving (Show, Eq)

parseIO :: String -> CharParser () a -> String -> Repl (Maybe a)
parseIO f p x = case parse (whiteSpace lambdaPi *> p <* eof) f x of
  Left  e -> liftIO $ print e >> return Nothing
  Right r -> return (Just r)

parseStmt :: [String] -> CharParser () Stmt
parseStmt e = choice [try define, assume, putstr, out, eval]
 where
  define = do
    reserved lambdaPi "let"
    q <- optionMaybe parseRig
    x <- identifier lambdaPi
    reserved lambdaPi "="
    t <- parseITerm OITerm e
    return (Let (fromMaybe RigW q) x t)
  assume = Assume . reverse <$> (reserved lambdaPi "assume" *> parseAssume)
  putstr =
    PutStrLn <$> (reserved lambdaPi "putStrLn" *> stringLiteral lambdaPi)
  out  = Out <$> (reserved lambdaPi "out" *> option "" (stringLiteral lambdaPi))
  eval = Eval <$> parseITerm OITerm e

parseRig :: CharParser () ZeroOneOmega
parseRig = choice
  [ Rig0 <$ reserved lambdaPi "0"
  , Rig1 <$ reserved lambdaPi "1"
  , RigW <$ reserved lambdaPi "w"
  ]

parseITerm :: Origin -> [String] -> CharParser () ITerm
parseITerm b e =
  choice
    $  [ try ann | b /= OAnn && b /= OApp ]
    ++ [ try $ parseApp e | b /= OApp ]
    ++ [var, parens lambdaPi $ parseITerm OITerm e]
 where
  ann =
    Ann
      <$> parseCTerm (if b == OCTerm then OStale else OAnn) e
      <*  reservedOp lambdaPi ":"
      <*> parseCTerm OAnn e
  var = do
    x <- identifier lambdaPi
    case elemIndex x e of
      Just n  -> return (Bound n)
      Nothing -> return (Free $ Global x)

parseCTerm :: Origin -> [String] -> CharParser () CTerm
parseCTerm b e =
  choice
    $  [ parseLam e
       , parseStar
       , try parsePi
       , try parsePair
       , try parseTensPr
       , try parsePairElim
       , try parseUnit
       , parseUnitType
       , parseUnitElim
       , parens lambdaPi $ parseCTerm OCTerm e
       ]
    ++ [ Inf <$> parseITerm b e | b /= OStale ]
 where
  parseStar = Star <$ reserved lambdaPi "*"
  parsePi   = do
    (e', (q, t)) <- parens lambdaPi $ parseBind e
    reservedOp lambdaPi "->"
    p <- parseCTerm OCTerm (e' : e)
    return (Pi q t p)
  parsePair =
    parens lambdaPi
      $   Pair
      <$> parseCTerm OCTerm e
      <*  reservedOp lambdaPi ","
      <*> parseCTerm OCTerm e
  parseTensPr = do
    (e', (q, t)) <- parens lambdaPi $ parseBind e
    reservedOp lambdaPi "*"
    p <- parseCTerm OCTerm (e' : e)
    return $ TensPr q t p
  parsePairElim = do
    reserved lambdaPi "let"
    x <- identifier lambdaPi
    reservedOp lambdaPi ","
    y <- identifier lambdaPi
    reservedOp lambdaPi "="
    m <- parseITerm OITerm e
    reserved lambdaPi "in"
    n <- parseCTerm OCTerm ([y, x] ++ e)
    return $ PairElim m n
  parseUnit     = Unit <$ reservedOp lambdaPi "(" <* reservedOp lambdaPi ")"
  parseUnitType = UnitType <$ reserved lambdaPi "Unit"
  parseUnitElim = do
    reserved lambdaPi "let"
    _ <- parseUnit
    reserved lambdaPi "="
    m <- parseITerm OITerm e
    reserved lambdaPi "in"
    n <- parseCTerm OCTerm e
    return $ UnitElim m n

parseLam :: [String] -> CharParser () CTerm
parseLam e = do
  reservedOp lambdaPi "\\"
  xs <- many1 (identifier lambdaPi)
  reservedOp lambdaPi "."
  t <- parseCTerm OCTerm (reverse xs ++ e)
  return (iterate Lam t !! length xs)

parseApp :: [String] -> CharParser () ITerm
parseApp e = foldl (:@:) <$> parseITerm OApp e <*> many1 (parseCTerm OApp e)

parseBind :: [String] -> CharParser () (String, (ZeroOneOmega, CTerm))
parseBind e = do
  q <- optionMaybe parseRig
  x <- identifier lambdaPi
  reservedOp lambdaPi ":"
  t <- parseCTerm OCTerm e
  return (x, (fromMaybe RigW q, t))

parseAssume :: CharParser () [(ZeroOneOmega, String, CTerm)]
parseAssume = snd <$> rec [] [] where
  rec
    :: [String]
    -> [(ZeroOneOmega, String, CTerm)]
    -> CharParser () ([String], [(ZeroOneOmega, String, CTerm)])
  rec e bs = do
    (x, (q, c)) <- parens lambdaPi $ parseBind []
    rec (x : e) ((q, x, c) : bs) <|> return (x : e, (q, x, c) : bs)

