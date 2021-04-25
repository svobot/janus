module Janus.Semiring
  ( Relevance(..)
  , Semiring(..)
  , ZeroOneMany(..)
  , extend
  ) where

data Relevance = Erased | Present deriving (Eq)

class Eq s => Semiring s where
  (.+.), (.*.), lub :: s -> s -> s
  infixr 6 .+.
  infixr 7 .*.

  zero, one :: s

  fitsIn :: s -> s -> Bool

  relevance :: s -> Relevance
  relevance s | s == zero = Erased
              | otherwise = Present

extend :: Semiring s => Relevance -> s
extend Erased  = zero
extend Present = one

data ZeroOneMany = Zero | One | Many deriving (Show, Eq)

instance Semiring ZeroOneMany where
  Zero .+. y    = y
  x    .+. Zero = x
  _    .+. _    = Many

  zero = Zero

  Zero .*. _    = Zero
  _    .*. Zero = Zero
  One  .*. One  = One
  _    .*. _    = Many

  one = One

  Zero `fitsIn` Many = True
  One  `fitsIn` Many = True
  x    `fitsIn` y    = x == y

  lub Zero Zero = Zero
  lub One  One  = One
  lub _    _    = Many

