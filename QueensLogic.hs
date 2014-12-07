{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE Rank2Types #-}

module QueensLogic where

import Control.Monad.Logic
import Data.List (intersect)

instance Show a => Show (Logic a) where
    show l = "Logic> " ++ (show $ observeAll l)

choices :: MonadLogic m => [a] -> m a
choices = msum . map return

-- K for Kleisli
type K m a = Monad m => (m a -> (a -> m a) -> m a)

data Diagonal
    = Row Int
    | Col Int
    | Backslash Int
    | Forwardslash Int
    deriving (Eq, Show)

type Square = (Int,Int)
type Queens = [Int] -- a configuration of nonattacking queens on the board
type Q = Queens

diags :: Square -> [Diagonal]
diags (i,j) = [ Row i
              , Col j
              , Backslash (j-i)
              , Forwardslash (i+j) ]

-- iswrt := "is safe with respect to"
-- iswrt :: (Int,Int) -> [Int] -> Bool
iswrt :: Square -> Q -> Bool
iswrt (i,j) qs = diags (i,j) `intersect` underThreat == []
  where
    qs' = zip [1..length qs] qs
    underThreat = qs' >>= diags

-- awtaoq := "all ways to add one queen"
-- we use a monad comprehension
awtaoq :: MonadLogic m => Int -> Q -> m Q
awtaoq n qs = [qs ++ [j] | j <- choices [1..n], (i,j) `iswrt` qs]
  where
    i = (length qs) + 1

queens :: MonadLogic m => Int -> K m Q -> m Q
queens n (>>~) = foldl (>>~) (return mzero) (replicate n (awtaoq n))
