{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LiberalTypeSynonyms #-}

module Interpreter
  ( repl
  ) where

import           Control.Monad.State            ( MonadIO
                                                , MonadState
                                                , evalStateT
                                                , foldM
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
import           Parser                         ( Stmt(..) )
import qualified Parser                        as Parse
import           Printer
import           Rig
import           Scope
import           System.Console.Repline  hiding ( options )
import           Text.PrettyPrint               ( render
                                                , text
                                                )
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
  return . filter (n `isPrefixOf`) $ scope

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
  liftIO $ maybe (return ()) (putStrLn . render . vPrint) t

browse :: Cmd Repl
browse _ = do
  (_, _, _, te) <- get
  liftIO . putStr $ unlines [ s | Global s <- reverse . nub $ map bndName te ]

compileFile :: Cmd Repl
compileFile f = do
  x     <- liftIO . readFile . dropWhile isSpace . dropWhileEnd isSpace $ f
  stmts <- Parse.file f x
  maybe (return ()) (foldM (const handleStmt) ()) stmts

handleStmt :: Stmt -> Repl ()
handleStmt stmt = case stmt of
  Assume ass -> foldM (const lpassume) () ass
  Let q x e  -> checkEval q x e
  Eval     e -> checkEval One it e
  PutStrLn x -> do
    liftIO $ putStrLn x
    return ()
  Out f -> modify $ \(inter, _, ve, te) -> (inter, f, ve, te)
 where
  it = "it"

  check :: ZeroOneMany -> ITerm -> ((Value, Value) -> Repl ()) -> Repl ()
  check q t kp = do
    --  typecheck and evaluate
    (_, _, ve, te) <- get
    x              <- iinfer (ve, te) q t
    case x of
      Nothing -> liftIO $ return ()
      Just y  -> do
        let v = iEval t (ve, [])
        kp (y, v)

  checkEval :: ZeroOneMany -> String -> ITerm -> Repl ()
  checkEval q i t = check
    q
    t
    (\(y, v) -> do
      --  ugly, but we have limited space in the paper
      --  usually, you'd want to have the bound identifier *and*
      --  the result of evaluation
      let outtext = if i == it
            then render
              (rPrint q <> text " " <> vPrint v <> text " :1 " <> vPrint y)
            else render
              (rPrint q <> text " " <> text i <> text " :2 " <> vPrint y)
      liftIO $ putStrLn outtext
      (_, out, _, _) <- get
      unless (null out) (liftIO $ writeFile out (process outtext))
      modify $ \(inter, _, ve, te) ->
        (inter, "", (Global i, v) : ve, Binding (Global i) q y : te)
    )

  process :: String -> String
  process = unlines . map ("< " ++) . lines

  lpassume :: Parse.Binding -> Repl ()
  lpassume (Binding x q t) = check
    Zero
    (Ann t Star)
    (\(_, v) -> do
      liftIO . putStrLn $ show q ++ " " ++ x ++ " : " ++ show v
      modify $ \(inter, out, ve, te) ->
        (inter, out, ve, Binding (Global x) q v : te)
      return ()
    )

