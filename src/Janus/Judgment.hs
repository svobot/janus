-- | Defines a 'Judgment' monad transformer that holds the context of
-- the judgment.
module Janus.Judgment
  ( Binding(..)
  , Context
  , TypingConfig(TypingConfig)
  , Judgment
  , evalInEnv
  , context
  , with
  , newLocalVar
  ) where

import           Control.Monad.Reader           ( ReaderT
                                                , asks
                                                )
import           Janus.Evaluation
import           Janus.Semiring
import           Janus.Syntax

-- | A context element grouping a variable name, its type, and quantity.
data Binding n u t = Binding
  { bndName  :: n
  , bndUsage :: u
  , bndType  :: t
  }
  deriving Eq

instance (Show n, Show u, Show t) => Show (Binding n u t) where
  show (Binding n u t) = show u <> " " <> show n <> " : " <> show t

-- | Judgment context.
type Context = [Binding Name ZeroOneMany Type]

-- | Record of variables that are in scope.
data TypingConfig = TypingConfig
  { -- | Variables which have been defined in some previous term. Their values
    -- are in 'ValueEnv' and their types in the 'Context'
    cfgGlobalContext :: (ValueEnv, Context)
  , -- | Variables which have a binding occurrence in the currently judged term.
    cfgBoundLocals   :: Context
  }

-- | Add new variable binding to the local environment.
with :: Binding Name ZeroOneMany Type -> TypingConfig -> TypingConfig
with b cfg = cfg { cfgBoundLocals = b : cfgBoundLocals cfg }

-- | Combine the contexts with global and local variables.
context :: TypingConfig -> Context
context (TypingConfig (_, globals) locals) = locals ++ globals

-- | A monad transformer which carries the context of a judgment.
type Judgment = ReaderT TypingConfig

-- | Evaluate the term in context provided by the judgment.
evalInEnv :: Monad m => CTerm -> Judgment m Value
evalInEnv m = asks (flip cEval m . (, []) . fst . cfgGlobalContext)

-- | Create a local variable with a fresh name.
newLocalVar :: Monad m => a -> b -> Judgment m (Binding Name a b)
newLocalVar s ty = do
  i <- asks $ length . cfgBoundLocals
  return $ Binding (Local i) s ty

