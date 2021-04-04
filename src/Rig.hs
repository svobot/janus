module Rig
  ( Relevance(..)
  , ZeroOneMany(..)
  , (<:)
  , extend
  ) where

import qualified Data.Semiring                 as S

data ZeroOneMany = Zero | One | Many deriving (Show, Eq)

instance S.Semiring ZeroOneMany where
  plus Zero a    = a
  plus a    Zero = a
  plus One  _    = Many
  plus _    One  = Many
  plus Many Many = Many

  times Zero _    = Zero
  times _    Zero = Zero
  times One  a    = a
  times a    One  = a
  times Many Many = Many

  zero = Zero
  one  = One

(<:) :: ZeroOneMany -> ZeroOneMany -> Bool
Zero <: Many = True
One  <: Many = True
x    <: y    = x == y

data Relevance = Erased | Present deriving (Eq)

extend :: S.Semiring s => Relevance -> s
extend Erased  = S.zero
extend Present = S.one

