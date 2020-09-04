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
  (haskellStyle { identStart    = letter <|> char '_'
                , reservedNames = ["forall", "let", "assume", "putStrLn", "out"]
                }
  )

type CharParser st = GenParser Char st

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
parseStmt e =
  do
      reserved lambdaPi "let"
      q <- optionMaybe parseRig
      x <- identifier lambdaPi
      reserved lambdaPi "="
      t <- parseApp e
      return (Let (fromMaybe RigW q) x t)
    <|> do
          reserved lambdaPi "assume"
          Assume . reverse <$> parseAssume
    <|> do
          reserved lambdaPi "putStrLn"
          x <- stringLiteral lambdaPi
          return (PutStrLn x)
    <|> do
          reserved lambdaPi "out"
          x <- option "" (stringLiteral lambdaPi)
          return (Out x)
    <|> do
          i <- parseApp e
          return $ Eval i

parseRig :: CharParser () ZeroOneOmega
parseRig = choice
  [ Rig0 <$ reserved lambdaPi "0"
  , Rig1 <$ reserved lambdaPi "1"
  , RigW <$ reserved lambdaPi "w"
  ]

parseITerm :: [String] -> CharParser () ITerm
parseITerm e =
  try
      (do
        t <- parens lambdaPi $ parseCTerm e
        reservedOp lambdaPi ":"
        t' <- parseCTerm e
        return (Ann t t')
      )
    <|> do
          x <- identifier lambdaPi
          case elemIndex x e of
            Just n  -> return (Bound n)
            Nothing -> return (Free (Global x))
    <|> parens lambdaPi (parseApp e)

parseCTerm :: [String] -> CharParser () CTerm
parseCTerm e = choice [parseStar, parsePi, parseLam e, Inf <$> parseITerm e]
 where
  parseStar = Star <$ reserved lambdaPi "*"
  parsePi   = do
    (e', (q, t)) <- parens lambdaPi $ parseBind e
    reservedOp lambdaPi "->"
    p <- parseCTerm (e' : e)
    return (Pi q t p)

parseLam :: [String] -> CharParser () CTerm
parseLam e = do
  reservedOp lambdaPi "\\"
  xs <- many1 (identifier lambdaPi)
  reservedOp lambdaPi "."
  t <- parseCTerm (reverse xs ++ e)
  return (iterate Lam t !! length xs)

parseApp :: [String] -> CharParser () ITerm
parseApp e = do
  t  <- parseITerm e
  ts <- many $ parseCTerm e
  return $ foldl (:@:) t ts

parseBind :: [String] -> CharParser () (String, (ZeroOneOmega, CTerm))
parseBind e = do
  q <- optionMaybe parseRig
  x <- identifier lambdaPi
  reservedOp lambdaPi ":"
  t <- parseCTerm e
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
