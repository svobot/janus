-- | Semiring class and instance definitions
module Janus.Semiring
  ( Relevance(..)
  , Semiring(..)
  , ZeroOneMany(..)
  , extend
  ) where

-- | Splits terms into computationally relevant ones and ones that can be used
-- only to form types.
data Relevance
   = -- | Expression has a computational presence.
     Erased
   | -- | Expression is only available for formation of types.
     Present
  deriving (Eq)

-- | The 'Semiring' class defines the basic operations over a semiring, a set
-- with two binary operations, '.+.' and '.*.', and two constants, 'zero' and
-- 'one'.
--
-- Instances of 'Semiring' should satisfy the following:
--
-- [Addition associativity]  @(a '.+.' b) '.+.' c  =  a '.+.' (b '.+.' c)@
-- [Addition identity] @'zero' '.+.' a  =  a@
-- [Addition commutativity]  @a '.+.' b  =  b '.+.' a@
-- [Multiplication associativity]  @(a '.*.' b) '.*.' c  =  a '.*.' (b '.*.' c)@
-- [Multiplication identity] @'one' '.*.' a  =  a  =  a '.*.' 'one'@
-- [Multiplication annihilation] @'zero' '.*.' a  =  'zero'  =  a '.*.' 'zero'@
-- [Left distributivity] @a '.*.' (b '.+.' c)  =  (a '.*.' b) '.+.' (a '.*.' c)@
-- [Right distributivity] @(a '.+.' b) '.*.' c  =  (a '.*.' c) '.+.' (b '.*.' c)@
class Eq s => Semiring s where
  (.+.), (.*.) :: s -> s -> s
  infixr 6 .+.
  infixr 7 .*.

  -- | Least upper bound of two elements.
  lub :: s -> s -> s

  zero, one :: s

  -- | Compare two elements using the partial ordering.
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

