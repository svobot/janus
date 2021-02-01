{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

module Interpreter
  ( repl
  ) where

import           Control.Exception              ( IOException
                                                , try
                                                )
import           Control.Monad.State            ( MonadIO
                                                , MonadState
                                                , evalStateT
                                                , gets
                                                , liftIO
                                                , modify
                                                , unless
                                                )
import           Data.Bifunctor                 ( bimap
                                                , second
                                                )
import           Data.Char                      ( isSpace )
import           Data.List                      ( dropWhileEnd
                                                , intercalate
                                                , isPrefixOf
                                                , nub
                                                )
import           Data.Maybe                     ( isNothing )
import qualified Data.Text                     as T
import qualified Data.Text.IO                  as T
import           Parser                         ( Stmt(..) )
import qualified Parser                        as Parse
import           Printer
import           Rig
import           Scope
import           System.Console.Repline  hiding ( options )
import           Types
import           Typing

data CmdInfo = CmdInfo
  { cmdNames  :: [String]
  , cmdArgs   :: Maybe String
  , cmdDesc   :: String
  , cmdAction :: Cmd Repl
  }

-- Evaluation : handle each line user inputs
compilePhrase :: Cmd Repl
compilePhrase x = do
  x' <- Parse.parseIO "<interactive>" (Parse.stmt []) x
  mapM_ handleStmt x'

-- Prefix tab completeter
defaultMatcher
  :: (MonadIO m, MonadState IState m) => [(String, CompletionFunc m)]
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
byWord :: (Monad m, MonadState IState m) => WordCompleter m
byWord n = do
  env <- gets $ snd . context
  let scope = [ s | Global s <- reverse . nub $ map bndName env ]
  return . filter (n `isPrefixOf`) $ scope ++ Parse.keywords

options :: [CmdInfo] -> [(String, Cmd Repl)]
options = concatMap $ traverse (,) <$> cmdNames <*> cmdAction

ini :: Repl ()
ini = liftIO $ putStrLn "Interpreter for Lambda-Pi.\nType :? for help."

final :: Repl ExitDecision
final = do
  liftIO $ putStrLn "Leaving Lambda-Pi interpreter."
  return Exit

commandPrefix :: Char
commandPrefix = ':'

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

-- Commands
commands :: [CmdInfo]
commands =
  [ CmdInfo ["type"] (Just "<expr>") "print type of expression" typeOf
  , CmdInfo ["browse"] Nothing "browse names in scope" browse
  , CmdInfo ["load"] (Just "<file>") "load program from file" compileFile
  , CmdInfo ["quit"] Nothing "exit interpreter" (const abort)
  , CmdInfo ["help", "?"] Nothing "display this list of commands" help
  ]

help :: Cmd Repl
help _ = liftIO $ do
  putStrLn
    "List of commands:  Any command may be abbreviated to its unique prefix.\n"
  putStr $ intercalate "\n" helpLines
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
typeOf x = do
  x'  <- Parse.parseIO "<interactive>" (Parse.iTerm Parse.OITerm []) x
  ctx <- gets context
  t   <- maybe (return Nothing) (iinfer ctx Zero) x'
  liftIO $ mapM_ (T.putStrLn . render . prettyAnsi) t

browse :: Cmd Repl
browse _ = do
  env <- gets $ snd . context
  liftIO . putStr $ unlines [ s | Global s <- reverse . nub $ map bndName env ]

compileFile :: Cmd Repl
compileFile f = do
  x' <-
    liftIO
    . ((try @IOException) . readFile)
    . dropWhile isSpace
    . dropWhileEnd isSpace
    $ f
  case x' of
    Left  e -> liftIO $ print e
    Right x -> Parse.file f x >>= mapM_ (mapM_ handleStmt)

handleStmt :: Stmt -> Repl ()
handleStmt stmt = case stmt of
  Assume bs  -> mapM_ assume bs
  Let q x e  -> checkEval q (Just x) e
  Eval     e -> checkEval One Nothing e
  PutStrLn x -> liftIO $ putStrLn x
  Out      f -> modify $ \st -> st { outFile = f }
 where
  checkEval :: ZeroOneMany -> Maybe String -> ITerm -> Repl ()
  checkEval q mn t = do
    ctx <- gets context
    mty <- iinfer ctx q t
    mapM_
      (\ty -> do
        let val     = iEval t (fst ctx, [])
        let outtext = renderRes mn (Binding val q ty)
        liftIO . T.putStrLn $ outtext
        out <- gets outFile
        unless
          (null out)
          (do
            let process = T.unlines . map ("< " <>) . T.lines
            liftIO . T.writeFile out $ process outtext
            modify $ \st -> st { outFile = "" }
          )
        mapM_
          (\i -> modify $ \st -> st
            { context = bimap ((Global i, val) :) (Binding (Global i) q ty :)
                          $ context st
            }
          )
          mn
      )
      mty

  assume :: Parse.Binding -> Repl ()
  assume (Binding x q t) = do
    let annt = Ann t Universe
    ctx <- gets context
    mty <- iinfer ctx Zero annt
    unless (isNothing mty) $ do
      let val = iEval annt (fst ctx, [])
      liftIO . T.putStrLn . renderRes Nothing $ Binding (vfree $ Global x) q val
      modify $ \st ->
        st { context = second (Binding (Global x) q val :) $ context st }
