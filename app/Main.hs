module Main
  ( main
  ) where

import           Janus.REPL
import           Janus.Style
import           Options.Applicative

opts :: ParserInfo Style
opts = info
  (unicodeFlag <**> helper)
  (  fullDesc
  <> progDesc "Run the Janus language REPL"
  <> header
       "janusc - an interpreter for Janus, a lamda-calculus with quantitative types"
  )
 where
  unicodeFlag :: Parser Style
  unicodeFlag = flag
    unicode
    ascii
    (long "ascii" <> short 'a' <> help "Disable pretty-printing in Unicode")

main :: IO ()
main = execParser opts >>= repl

