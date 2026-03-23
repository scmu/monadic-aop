{-# OPTIONS_GHC -Wno-missing-methods #-}

module Common where

import Prelude hiding (max)
import Control.Applicative
import Control.Monad

(===) :: a -> a -> a
(===) = undefined

infixr 0 ===

data P a = P

instance Functor P where
instance Applicative P where
instance Monad P where
instance Alternative P where
instance MonadPlus P where
instance MonadFail P where

type List a = [a]

infixr 0 `sse`

sse :: a -> a -> a
sse = undefined

infixr 0 `spse`

spse :: a -> a -> a
spse = undefined

any :: P a
any = undefined

max :: P a -> P a
max = undefined

max_unlhd :: P a -> P a
max_unlhd = max
