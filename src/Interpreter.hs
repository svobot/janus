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
                                                , get
                                                , liftIO
                                                , modify
                                                , unless
                                                )
import           Data.Char                      ( isSpace )
import           Data.List                      ( dropWhileEnd
                                                , intercalate
                                                , isPrefixOf
                                                , nub
                                                )
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
  maybe (return ()) handleStmt x'

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
  (_, _, _, te) <- get
  let scope = [ s | Global s <- reverse . nub $ map bndName te ]
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
repl = flip evalStateT (True, [], [], []) $ evalRepl
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
  x' <- Parse.parseIO "<interactive>" (Parse.iTerm Parse.OITerm []) x
  (_, _, ve, te) <- get
  t <- maybe (return Nothing) (iinfer (ve, te) Zero) x'
  liftIO $ mapM_ (T.putStrLn . render . prettyAnsi) t

browse :: Cmd Repl
browse _ = do
  (_, _, _, te) <- get
  liftIO . putStr $ unlines [ s | Global s <- reverse . nub $ map bndName te ]

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
  Assume ass -> mapM_ lpassume ass
  Let q x e  -> checkEval q (Just x) e
  Eval     e -> checkEval One Nothing e
  PutStrLn x -> liftIO $ putStrLn x
  Out      f -> modify $ \(inter, _, ve, te) -> (inter, f, ve, te)
 where
  check :: ZeroOneMany -> ITerm -> ((Value, Type) -> Repl ()) -> Repl ()
  check q t kp = do
    --  typecheck and evaluate
    (_, _, ve, te) <- get
    x              <- iinfer (ve, te) q t
    mapM_ (kp . (iEval t (ve, []), )) x

  checkEval :: ZeroOneMany -> Maybe String -> ITerm -> Repl ()
  checkEval q mi t = check
    q
    t
    (\(val, ty) -> do
      let outtext = renderRes (Binding mi q ty) val
      liftIO . T.putStrLn $ outtext
      (_, out, _, _) <- get
      unless
        (null out)
        (do
          let process = T.unlines . map ("< " <>) . T.lines
          liftIO . T.writeFile out $ process outtext
          modify $ \(i, _, ve, te) -> (i, "", ve, te)
        )
      mapM_
        (\i -> modify $ \(inter, o, ve, te) ->
          (inter, o, (Global i, val) : ve, Binding (Global i) q ty : te)
        )
        mi
    )

  lpassume :: Parse.Binding -> Repl ()
  lpassume (Binding x q t) = check
    Zero
    (Ann t Star)
    (\(val, _) -> do
      liftIO . T.putStrLn $ renderRes (Binding Nothing q val) (vfree $ Global x)
      modify $ \(inter, out, ve, te) ->
        (inter, out, ve, Binding (Global x) q val : te)
      return ()
    )

