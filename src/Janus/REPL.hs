{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Janus.REPL
  ( IState(..)
  , MonadAbstractIO(..)
  , compilePhrase
  , repl
  ) where

import           Control.Exception              ( IOException
                                                , try
                                                )
import           Control.Monad.State            ( MonadIO
                                                , MonadState(..)
                                                , StateT
                                                , evalStateT
                                                , forM_
                                                , gets
                                                , liftIO
                                                , modify
                                                , unless
                                                )
import           Data.Bifunctor                 ( bimap
                                                , second
                                                )
import           Data.Char                      ( isSpace )
import           Data.Function                  ( on )
import           Data.List                      ( dropWhileEnd
                                                , intercalate
                                                , isPrefixOf
                                                , nub
                                                , nubBy
                                                )
import           Data.Maybe                     ( isNothing )
import qualified Data.Text                     as T
import qualified Data.Text.IO                  as T
import           Janus.Parser
import           Janus.Printer
import           Janus.Semiring
import           Janus.Types
import           Janus.Typing
import           System.Console.Repline  hiding ( options )
import           Text.Parsec                    ( ParseError )

class (Monad m) => MonadAbstractIO m where
  output :: String -> m ()
  outputDoc :: Doc -> m ()
  outputFile :: FilePath -> T.Text -> m ()

instance (Monad m, MonadIO m) => MonadAbstractIO (HaskelineT m) where
  output     = liftIO . putStrLn
  outputDoc  = liftIO . T.putStrLn . render
  outputFile = (liftIO .) . T.writeFile

data IState = IState
  { outFile :: String
  , context :: Context
  }

type Repl = HaskelineT (StateT IState IO)

type AbstractRepl m = (MonadState IState m, MonadAbstractIO m)

commandPrefix :: Char
commandPrefix = ':'

-- Prefix tab completeter
defaultMatcher :: (MonadIO m) => [(String, CompletionFunc m)]
defaultMatcher =
  [ (commandPrefix : "load ", fileCompleter)
  , (commandPrefix : "l "   , fileCompleter)
  , ([commandPrefix]        , wordCompleter commandCompleter)
  ]

commandCompleter :: Monad m => WordCompleter m
commandCompleter n =
  return
    . filter (n `isPrefixOf`)
    . map (commandPrefix :)
    . concatMap cmdNames
    $ commands

-- Default tab completer
byWord :: (MonadState IState m) => WordCompleter m
byWord n = do
  env <- gets $ snd . context
  let scope = [ s | Global s <- reverse . nub $ map bndName env ]
  return . filter (n `isPrefixOf`) $ scope ++ keywords

data CmdInfo = CmdInfo
  { cmdNames  :: [String]
  , cmdArgs   :: Maybe String
  , cmdDesc   :: String
  , cmdAction :: Cmd Repl
  }

-- Commands
commands :: [CmdInfo]
commands =
  [ CmdInfo ["type"] (Just "<expr>") "print type of expression" typeOf
  , CmdInfo ["browse"] Nothing "browse names in scope" browse
  , CmdInfo ["load"] (Just "<file>") "load program from file" compileFile
  , CmdInfo ["quit"] Nothing "exit interpreter" (const abort)
  , CmdInfo ["help", "?"] Nothing "display this list of commands" help
  ]

options :: [CmdInfo] -> [(String, Cmd Repl)]
options = concatMap $ traverse (,) <$> cmdNames <*> cmdAction

help :: Cmd Repl
help _ = liftIO $ do
  putStrLn
    "List of commands:  Any command may be abbreviated to its unique prefix.\n"
  putStrLn $ intercalate "\n" helpLines
 where
  aliases args =
    intercalate ", " . map ((++ maybe "" (' ' :) args) . (commandPrefix :))
  cols =
    [ ("<expr>"               , "evaluate expression")
      , ("let <var> = <expr>"   , "define variable")
      , ("assume <var> : <expr>", "assume variable\n")
      ]
      ++ map ((,) <$> (aliases <$> cmdArgs <*> cmdNames) <*> cmdDesc) commands
  spaces colWidth cmd = replicate (colWidth + 2 - length cmd) ' '
  fmt w (c, desc) = c <> spaces w c <> desc
  helpLines = map (fmt . maximum $ map (length . fst) cols) cols

typeOf :: Cmd Repl
typeOf s = do
  mx  <- parseIO typeParser s
  ctx <- gets context
  t   <- maybe (return Nothing) (uncurry (iinfer ctx)) mx
  mapM_ (liftIO . T.putStrLn . render . pretty) t

browse :: Cmd Repl
browse _ = do
  env <- gets $ snd . context
  mapM_ (liftIO . T.putStrLn . render . pretty)
    . reverse
    . map (\b -> b { bndName = vfree $ bndName b })
    $ nubBy ((==) `on` bndName) env

-- Evaluation : handle each line user inputs
compilePhrase :: AbstractRepl m => String -> m ()
compilePhrase x = do
  x' <- parseIO evalParser x
  mapM_ handleStmt x'

compileFile :: Cmd Repl
compileFile f = do
  x' <-
    liftIO
    . (try @IOException . readFile)
    . dropWhile isSpace
    . dropWhileEnd isSpace
    $ f
  case x' of
    Left  e -> liftIO $ print e
    Right x -> parseIO (fileParser f) x >>= mapM_ (mapM_ handleStmt)

iinfer :: AbstractRepl m => Context -> ZeroOneMany -> ITerm -> m (Maybe Type)
iinfer g r t = case synthesise g r t of
  Left  e -> outputDoc (pretty e) >> return Nothing
  Right v -> return (Just v)

parseIO :: MonadAbstractIO m => (a -> Either ParseError b) -> a -> m (Maybe b)
parseIO p x = case p x of
  Left  e -> output (show e) >> return Nothing
  Right r -> return (Just r)

handleStmt :: AbstractRepl m => Stmt -> m ()
handleStmt stmt = case stmt of
  Assume bs  -> mapM_ assume bs
  Let q x e  -> checkEval q (Just x) e
  Eval q e   -> checkEval q Nothing e
  PutStrLn x -> output x
  Out      f -> modify $ \st -> st { outFile = f }
 where
  mapContext f = \st -> st { context = f $ context st }

  assume (Binding x q t) = do
    let annt = Ann t Universe
    ctx <- gets context
    mty <- iinfer ctx Zero annt
    unless (isNothing mty) $ do
      let val = iEval annt (fst ctx, [])
      outputDoc . pretty $ Binding (vfree $ Global x) q val
      modify . mapContext $ second (Binding (Global x) q val :)

  checkEval q mn t = do
    ctx <- gets context
    mty <- iinfer ctx q t
    forM_ mty $ \ty -> do
      let val = iEval t (fst ctx, [])
      let outdoc =
            pretty q
              <+> maybe mempty ((<+> "= ") . var . pretty . T.pack) mn
              <>  pretty (Ann (quote0 val) (quote0 ty))
      outputDoc outdoc
      out <- gets outFile
      unless (null out) $ do
        let process = T.unlines . map ("< " <>) . T.lines
        outputFile out . process $ render outdoc
        modify $ \st -> st { outFile = "" }
      forM_ mn $ \n -> modify . mapContext $ bimap ((Global n, val) :)
                                                   (Binding (Global n) q ty :)

ini :: Repl ()
ini = liftIO $ putStrLn "Interpreter for Janus.\nType :? for help."

final :: Repl ExitDecision
final = do
  liftIO $ putStrLn "Leaving Janus interpreter."
  return Exit

repl :: IO ()
repl = flip evalStateT (IState "" ([], [])) $ evalRepl
  (const $ pure ">>> ")
  compilePhrase
  (options commands)
  (Just commandPrefix)
  Nothing
  (Combine (Prefix (wordCompleter byWord) defaultMatcher)
           (Word commandCompleter)
  )
  ini
  final

