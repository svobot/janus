module Parser where

import           Control.Monad.Trans            ( liftIO )
import           Data.List                      ( elemIndex )
import           Text.Parsec
import           Text.Parsec.String             ( GenParser )
import           Text.Parsec.Token
import           Text.Parsec.Language           ( haskellStyle )
import           Types

simplyTyped = makeTokenParser
  (haskellStyle { identStart    = letter <|> char '_'
                , reservedNames = ["let", "assume", "putStrLn"]
                }
  )

lambdaPi = makeTokenParser
  (haskellStyle { identStart    = letter <|> char '_'
                , reservedNames = ["forall", "let", "assume", "putStrLn", "out"]
                }
  )

type CharParser st = GenParser Char st

data Stmt = Let String ITerm               --  let x = t
                 | Assume [(String,CTerm)] --  assume x :: t, assume x :: *
                 | Eval ITerm
                 | PutStrLn String         --  lhs2TeX hacking, allow to print "magic" string
                 | Out String              --  more lhs2TeX hacking, allow to print to files
  deriving (Show)


parseStmt_ :: [String] -> CharParser () Stmt
parseStmt_ e =
  do
      reserved lambdaPi "let"
      x <- identifier lambdaPi
      reserved lambdaPi "="
      t <- parseITerm_ 0 e
      return (Let x t)
    <|> do
          reserved lambdaPi "assume"
          (xs, ts) <- parseBindings_ False []
          return (Assume (reverse (zip xs ts)))
    <|> do
          reserved lambdaPi "putStrLn"
          x <- stringLiteral lambdaPi
          return (PutStrLn x)
    <|> do
          reserved lambdaPi "out"
          x <- option "" (stringLiteral lambdaPi)
          return (Out x)
    <|> fmap Eval (parseITerm_ 0 e)

parseBindings_ :: Bool -> [String] -> CharParser () ([String], [CTerm])
parseBindings_ b e =
  (let rec :: [String] -> [CTerm] -> CharParser () ([String], [CTerm])
       rec e ts = do
         (x, t) <- parens
           lambdaPi
           (do
             x <- identifier lambdaPi
             reserved lambdaPi "::"
             t <- parseCTerm_ 0 (if b then e else [])
             return (x, t)
           )
         rec (x : e) (t : ts) <|> return (x : e, t : ts)
   in  rec e []
    )
    <|> do
          x <- identifier lambdaPi
          reserved lambdaPi "::"
          t <- parseCTerm_ 0 e
          return (x : e, [t])

parseITerm_ :: Int -> [String] -> CharParser () ITerm
parseITerm_ 0 e =
  do
      reserved lambdaPi "forall"
      (fe, t : ts) <- parseBindings_ True e
      reserved lambdaPi "."
      t' <- parseCTerm_ 0 fe
      return (foldl (\p t -> Pi t (Inf p)) (Pi t t') ts)
    <|> try
          (do
            t <- parseITerm_ 1 e
            rest (Inf t) <|> return t
          )
    <|> do
          t <- parens lambdaPi (parseLam_ e)
          rest t
 where
  rest t = do
    reserved lambdaPi "->"
    t' <- parseCTerm_ 0 ([] : e)
    return (Pi t t')
parseITerm_ 1 e =
  try
      (do
        t <- parseITerm_ 2 e
        rest (Inf t) <|> return t
      )
    <|> do
          t <- parens lambdaPi (parseLam_ e)
          rest t
 where
  rest t = do
    reserved lambdaPi "::"
    t' <- parseCTerm_ 0 e
    return (Ann t t')
parseITerm_ 2 e = do
  t  <- parseITerm_ 3 e
  ts <- many (parseCTerm_ 3 e)
  return (foldl (:@:) t ts)
parseITerm_ 3 e =
  do
      reserved lambdaPi "*"
      return Star
    <|> do
          n <- natural lambdaPi
          return (toNat_ n)
    <|> do
          x <- identifier lambdaPi
          case elemIndex x e of
            Just n  -> return (Bound n)
            Nothing -> return (Free (Global x))
    <|> parens lambdaPi (parseITerm_ 0 e)
parseITerm_ _ _ = error "TODO" --TODO fix?

toNat_ :: Integer -> ITerm
toNat_ n = Ann (toNat_' n) (Inf Nat)
 where
  toNat_' :: Integer -> CTerm
  toNat_' 0  = Zero
  toNat_' n' = Succ (toNat_' (n' - 1))

parseCTerm_ :: Int -> [String] -> CharParser () CTerm
parseCTerm_ 0 e = parseLam_ e <|> fmap Inf (parseITerm_ 0 e)
parseCTerm_ p e =
  try (parens lambdaPi (parseLam_ e)) <|> fmap Inf (parseITerm_ p e)

parseLam_ :: [String] -> CharParser () CTerm
parseLam_ e = do
  reservedOp lambdaPi "\\"
  xs <- many1 (identifier lambdaPi)
  reservedOp lambdaPi "->"
  t <- parseCTerm_ 0 (reverse xs ++ e)
  --  reserved lambdaPi "."
  return (iterate Lam t !! length xs)

parseIO :: String -> CharParser () a -> String -> Repl (Maybe a)
parseIO f p x =
  case parse (whiteSpace simplyTyped >> p >>= \x -> eof >> return x) f x of
    Left  e -> liftIO $ print e >> return Nothing
    Right r -> return (Just r)

