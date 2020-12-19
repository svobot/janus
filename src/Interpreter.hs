{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE TupleSections #-}

module Interpreter
  ( repl
  ) where

import           Control.Monad                  ( unless )
import           Control.Monad.State.Lazy       ( MonadIO
                                                , MonadState
                                                , evalStateT
                                                , foldM
                                                , get
                                                , modify
                                                )
import           Control.Monad.Trans            ( liftIO )
import           Data.List                      ( intercalate
                                                , isPrefixOf
                                                , nub
                                                )
import           Data.List.Extra                ( trim )
import           Parser                         ( Stmt(..) )
import qualified Parser                        as Parse
import           Printer
import           Rig
import           Scope
import           System.Console.Repline  hiding ( options )
import           Text.Parsec                    ( many )
import           Text.PrettyPrint               ( render
                                                , text
                                                )
import           Types
import           Typing

data CommandInfo = CmdInfo [String] String String (Cmd Repl)

-- Evaluation : handle each line user inputs
compilePhrase :: Cmd Repl
compilePhrase x = do
  x' <- Parse.parseIO "<interactive>" (Parse.stmt []) x
  maybe (return ()) handleStmt x'

-- Prefix tab completeter
defaultMatcher :: MonadIO m => [(String, CompletionFunc m)]
defaultMatcher = [(":load", fileCompleter)]

-- Default tab completer
byWord :: (Monad m, MonadState IState m) => WordCompleter m
byWord n = do
  (_, _, _, te) <- get
  let scope = [ s | Global s <- reverse . nub $ map bndName te ]
  let cmds =
        map (commandPrefix :) $ concatMap (\(CmdInfo cs _ _ _) -> cs) commands
  return . filter (isPrefixOf n) $ cmds ++ scope

options :: [CommandInfo] -> [(String, Cmd Repl)]
options = concatMap (\(CmdInfo cmds _ _ c) -> map (, c) cmds)

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
  (Prefix (wordCompleter byWord) defaultMatcher)
  ini
  final

-- Commands
commands :: [CommandInfo]
commands =
  [ CmdInfo ["type"]      "<expr>" "print type of expression"      typeOf
  , CmdInfo ["browse"]    ""       "browse names in scope"         browse
  , CmdInfo ["load"]      "<file>" "load program from file"        compileFile
  , CmdInfo ["quit"]      ""       "exit interpreter"              (const abort)
  , CmdInfo ["help", "?"] ""       "display this list of commands" help
  ]

help :: Cmd Repl
help _ = liftIO . putStr $ helpTxt commands
 where
  helpTxt :: [CommandInfo] -> String
  helpTxt cs =
    "List of commands:  Any command may be abbreviated to its unique prefix.\n\n"
      ++ "<expr>                  evaluate expression\n"
      ++ "let <var> = <expr>      define variable\n"
      ++ "assume <var> :: <expr>  assume variable\n\n"
      ++ unlines
           (map
             (\(CmdInfo cmds a d _) ->
               let
                 ct = intercalate
                   ", "
                   (map
                     ((++ if null a then "" else " " ++ a) . (commandPrefix :))
                     cmds
                   )
               in  ct ++ replicate ((24 - length ct) `max` 2) ' ' ++ d
             )
             cs
           )

typeOf :: Cmd Repl
typeOf x = do
  x' <- Parse.parseIO "<interactive>" (Parse.iTerm Parse.OITerm []) x
  (_, _, ve, te) <- get
  t <- maybe (return Nothing) (iinfer (ve, te) Zero) x'
  liftIO $ maybe (return ()) (putStrLn . render . itprint) t

browse :: Cmd Repl
browse _ = do
  (_, _, _, te) <- get
  liftIO . putStr $ unlines [ s | Global s <- reverse . nub $ map bndName te ]

compileFile :: Cmd Repl
compileFile f = do
  x     <- liftIO . readFile $ trim f
  stmts <- Parse.parseIO f (many $ Parse.stmt []) x
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
      let outtext = show q ++ " " ++ if i == it
            then render (itprint v <> text " :: " <> itprint y)
            else render (text i <> text " :: " <> itprint y)
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

