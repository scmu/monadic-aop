{-# OPTIONS_GHC -Wno-missing-methods #-}

module Common where

import Prelude hiding (max)
import Control.Applicative
import Control.Monad

import Test.QuickCheck hiding ((===), collect)


(===) :: a -> a -> a
(===) = undefined

infixr 0 ===

newtype P a = P (List a)
 deriving (Show, Eq)

unP :: P a -> List a
unP (P xs) = xs

instance Functor P where
  fmap f (P xs) = P (map f xs)

instance Applicative P where
  pure x = P [x]
  P fs <*> P xs = P (fs <*> xs)

instance Monad P where
  return = pure
  P xs >>= f = joinP (map f xs)
    where joinP xss = P (concat (map unP xss))

instance Alternative P where
  empty = P []
  P xs <|> P ys = P (xs ++ ys )

instance MonadPlus P where
  mzero = empty
  mplus = (<|>)

instance MonadFail P where
  fail _ = mzero

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

-- QuickCheck Stuffs

atMost :: Int -> Gen Int
atMost n = fmap ((`mod` n) . abs) arbitrary

listNoLongerThan :: Int -> Gen a -> Gen [a]
listNoLongerThan n g = do
  m <- atMost n
  replicateM m g
