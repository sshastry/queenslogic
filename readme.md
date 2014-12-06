
# Introduction

The aim of these notes is to use the n queens problem to give an example of the use of the logic monad. The logic monad was introduced in paper "Backtracking, interleaving, and terminating monad transformers: (functional pearl)" by Oleg Kiselyov, Chung-chieh Shan, Daniel P. Friedman, Amr Sabry (available [here](http://okmij.org/ftp/papers/LogicT.pdf)). I originally learned of the logic monad from the paper "Adventures in Three Monads" by Edward Z. Yang in [The Monad Reader Issue 15](http://themonadreader.files.wordpress.com/2010/01/issue15.pdf).

The examples in those papers seemed a bit complicated to me. The first backtracking algorithm I learned was the solution to the n queens problem, so I wondered what I could see by solving that using the logic monad.

Let's first briefly explain what the logic monad is for.

## Logic

(Note: this document mixes code from QueensLogic.hs and fair.hs with repl sessions.)

Besides being used for collections, the list type Haskell is used to represent a nondeterministic value. For example `xs :: [Integer]` might mean a finite ordered sequence of integers, or it might mean one of many unknown integers i.e. a single nondeterministic integer. The latter semantics is illustrated by the following
```haskell
>>> import Control.Applicative
>>> (+) <$> [1,2,3] <*> [10,20,30]
[11,21,31,12,22,32,13,23,33]
```
which means
> if we add a value which may be 1,2, or 3 to a value which may be 10,20, or 30 we get a value which may be 11,21,31,12,22,32,13,23, or 33.

If we naively build up a nondeterministic value using `(++)` and `(>>=)` for the list monad, we might encounter the following problem (example taken from the paper by Kiselyov et al).

```haskell
odds :: [Integer]
odds = (return 1) ++ (odds >>= \x -> [x+2])

ts :: [Integer]
ts = [10] ++ [20] ++ [30]

z :: Integer
z = head $ (odds ++ ts) >>= (\x -> if even x then [x] else [])
```

If we load this into ghci and try to evaluate z, we find that ghci hangs. This is unfortunate, since z should be equal to 10, the first even number in the list `odds ++ [ts]`. The problem is that `(++)` is *unfair* in the sense that it demands that all of the elements of its first argument be shoved through the `(>>=)` before its second argument gets a chance. Let's rewrite the above with the logic monad as follows.

```haskell
import Control.Monad.Logic

odds0 :: Logic Integer
odds0 = (return 1) `mplus` (odds0 >>= \x -> return (x+2))

ts0 :: Logic Integer
ts0 = msum (map return [10,20,30])

z0 :: Integer
z0 = observe $ (odds0 `interleave` ts0) >>= (\x -> if even x then return x else mzero)
```

In the repl:

```haskell
>>> z
^CInterrupted.
>>> z0
10
>>>
```

That, in a nutshell, is the point of the logic monad, or rather of `MonadPlus` instances which are made into instances of `MonadLogic`. On such instances, we have fair versions of `mplus` and `(>>=)` which are denoted `interleave` and `(>>-)` respectively (so we can still use the unfair `mplus` and `(>>=)` if we need them).

The above example doesn't explain when to use `(>>-)` instead of `(>>=)`; I'll refer to the paper by Kiselyov et al for more on that.

## n queens

The problem is well known, see [here](http://en.wikipedia.org/wiki/Eight_queens_puzzle) for a description. There is a solution to this problem in Haskell using list comprehensions [here](https://www.haskell.org/haskellwiki/99_questions/Solutions/90). That solution makes use of `[[Int]]` to represent a nondeterministic value of a collection of integers, thus using the list type with two different meanings. Let's tease apart the two meanings so that we can use the same code with both the list and logic monads.

Starting from scratch:

```haskell
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE Rank2Types #-}

module QueensLogic where

import Control.Monad.Logic
import Data.List (intersect, (\\))

instance Show a => Show (Logic a) where
    show l = "Logic> " ++ (show $ observeAll l)

choices :: MonadLogic m => [a] -> m a
choices = msum . map return

-- K is for Kleisli
type K m a = Monad m => (m a -> (a -> m a) -> m a)
```

Now we get to the problem at hand. We index rows and cols and diagonals by integers. The terminology is unorthodox in that we regard rows and cols as degenerate diagonals.

```haskell
data Diagonal
    = Row Int
    | Col Int
    | Backslash Int
    | Forwardslash Int
    deriving (Eq, Show)
```

Given a position `(i,j)` on the board, we send it to the list [Row, Col, Backslash, Forwardslash] containing it. We have chosen the numbering of diagonals so that there is no need to pass in the global board size. Note that the type Queens is meant to be a collection (not a nondeterministic value) of integers, such that the ith element of the list is j iff there is a queen at position `(i,j)`.

```haskell
type Square = (Int,Int)
type Queens = [Int] -- a configuration of nonattacking queens on the board
type Q = Queens -- save some typing

diags :: Square -> [Diagonal]
diags (i,j) = [ Row i
              , Col j
              , Backslash (j-i)
              , Forwardslash (i+j) ]

-- iswrt := "is safe with respect to"
iswrt :: Square -> Q -> Bool
iswrt (i,j) qs = diags (i,j) `intersect` underThreat == []
  where
    qs' = zip [1..length qs] qs
    underThreat = qs' >>= diags
```

The following function is the inductive step of the algorithm. Given an admissible placement `qs` of queens, where the length of `qs` is strictly less than the dimension `n` of the board, `awtaoq` returns a nondeterministic value of all of the ways to extend `qs` by one more queen and still have an admissible placement of queens on the board. Using a monad comprehension (link?) is how we enforce our chosen notion of nondeterminism.

```haskell
-- awtaoq := "all ways to add one queen"
awtaoq :: MonadLogic m => Int -> Q -> m Q
awtaoq n qs = [qs ++ [j] | j <- choices [1..n], (i,j) `iswrt` qs]
  where
    i = (length qs) + 1
```

Finally, we compute all possible solutions by actually performing the inductive construction, here expressed by a `foldl`.

```haskell
queens :: MonadLogic m => Int -> K m Q -> m Q
queens n (>>~) = foldr (>>~) (return mzero) (replicate n (awtaoq n))
```

Due to how we've factored the code, we can observe the difference between how the list monad traverses the search space, and how the logic monad traverses the search space. Here's how list traverses with `(>>=)` (output formatted for readability):

```haskell
>>> queens 8 (>>=) :: [Q]
[[1,5,8,6,3,7,2,4],[1,6,8,3,7,4,2,5],[1,7,4,6,8,2,5,3],[1,7,5,8,2,4,6,3],[2,4,6,8,3,1,7,5],
 [2,5,7,1,3,8,6,4],[2,5,7,4,1,8,6,3],[2,6,1,7,4,8,3,5],[2,6,8,3,1,4,7,5],[2,7,3,6,8,5,1,4],
 [2,7,5,8,1,4,6,3],[2,8,6,1,3,5,7,4],[3,1,7,5,8,2,4,6],[3,5,2,8,1,7,4,6],[3,5,2,8,6,4,7,1],
 [3,5,7,1,4,2,8,6],[3,5,8,4,1,7,2,6],[3,6,2,5,8,1,7,4],[3,6,2,7,1,4,8,5],[3,6,2,7,5,1,8,4],
 [3,6,4,1,8,5,7,2],[3,6,4,2,8,5,7,1],[3,6,8,1,4,7,5,2],[3,6,8,1,5,7,2,4],[3,6,8,2,4,1,7,5],
 [3,7,2,8,5,1,4,6],[3,7,2,8,6,4,1,5],[3,8,4,7,1,6,2,5],[4,1,5,8,2,7,3,6],[4,1,5,8,6,3,7,2],
 [4,2,5,8,6,1,3,7],[4,2,7,3,6,8,1,5],[4,2,7,3,6,8,5,1],[4,2,7,5,1,8,6,3],[4,2,8,5,7,1,3,6],
 [4,2,8,6,1,3,5,7],[4,6,1,5,2,8,3,7],[4,6,8,2,7,1,3,5],[4,6,8,3,1,7,5,2],[4,7,1,8,5,2,6,3],
 [4,7,3,8,2,5,1,6],[4,7,5,2,6,1,3,8],[4,7,5,3,1,6,8,2],[4,8,1,3,6,2,7,5],[4,8,1,5,7,2,6,3],
 [4,8,5,3,1,7,2,6],[5,1,4,6,8,2,7,3],[5,1,8,4,2,7,3,6],[5,1,8,6,3,7,2,4],[5,2,4,6,8,3,1,7],
 [5,2,4,7,3,8,6,1],[5,2,6,1,7,4,8,3],[5,2,8,1,4,7,3,6],[5,3,1,6,8,2,4,7],[5,3,1,7,2,8,6,4],
 [5,3,8,4,7,1,6,2],[5,7,1,3,8,6,4,2],[5,7,1,4,2,8,6,3],[5,7,2,4,8,1,3,6],[5,7,2,6,3,1,4,8],
 [5,7,2,6,3,1,8,4],[5,7,4,1,3,8,6,2],[5,8,4,1,3,6,2,7],[5,8,4,1,7,2,6,3],[6,1,5,2,8,3,7,4],
 [6,2,7,1,3,5,8,4],[6,2,7,1,4,8,5,3],[6,3,1,7,5,8,2,4],[6,3,1,8,4,2,7,5],[6,3,1,8,5,2,4,7],
 [6,3,5,7,1,4,2,8],[6,3,5,8,1,4,2,7],[6,3,7,2,4,8,1,5],[6,3,7,2,8,5,1,4],[6,3,7,4,1,8,2,5],
 [6,4,1,5,8,2,7,3],[6,4,2,8,5,7,1,3],[6,4,7,1,3,5,2,8],[6,4,7,1,8,2,5,3],[6,8,2,4,1,7,5,3],
 [7,1,3,8,6,4,2,5],[7,2,4,1,8,5,3,6],[7,2,6,3,1,4,8,5],[7,3,1,6,8,5,2,4],[7,3,8,2,5,1,6,4],
 [7,4,2,5,8,1,3,6],[7,4,2,8,6,1,3,5],[7,5,3,1,6,8,2,4],[8,2,4,1,7,5,3,6],[8,2,5,3,1,7,4,6],
 [8,3,1,6,2,5,7,4],[8,4,1,3,6,2,7,5]]
```

Here's how logic does it using the fair operation `(>>-)`:

```haskell
>>> queens 8 (>>-) :: Logic Q
Logic> [[2,4,6,8,3,1,7,5],[3,1,7,5,8,2,4,6],[1,5,8,6,3,7,2,4],[2,5,7,1,3,8,6,4],[2,5,7,4,1,8,6,3],
        [1,6,8,3,7,4,2,5],[4,1,5,8,2,7,3,6],[4,1,5,8,6,3,7,2],[2,6,1,7,4,8,3,5],[1,7,4,6,8,2,5,3],
        [1,7,5,8,2,4,6,3],[3,5,2,8,1,7,4,6],[2,6,8,3,1,4,7,5],[3,5,2,8,6,4,7,1],[3,5,7,1,4,2,8,6],
        [5,1,4,6,8,2,7,3],[3,5,8,4,1,7,2,6],[2,7,3,6,8,5,1,4],[2,7,5,8,1,4,6,3],[5,1,8,4,2,7,3,6],
        [3,6,2,5,8,1,7,4],[3,6,2,7,1,4,8,5],[3,6,2,7,5,1,8,4],[5,1,8,6,3,7,2,4],[4,2,5,8,6,1,3,7],
        [2,8,6,1,3,5,7,4],[3,6,4,1,8,5,7,2],[3,6,4,2,8,5,7,1],[3,6,8,1,4,7,5,2],[3,6,8,1,5,7,2,4],
        [3,7,2,8,5,1,4,6],[3,6,8,2,4,1,7,5],[4,2,7,3,6,8,1,5],[3,7,2,8,6,4,1,5],[4,2,7,3,6,8,5,1],
        [4,2,7,5,1,8,6,3],[4,2,8,6,1,3,5,7],[4,2,8,5,7,1,3,6],[6,1,5,2,8,3,7,4],[4,6,1,5,2,8,3,7],
        [3,8,4,7,1,6,2,5],[5,2,4,6,8,3,1,7],[5,2,4,7,3,8,6,1],[4,6,8,2,7,1,3,5],[5,2,6,1,7,4,8,3],
        [4,7,1,8,5,2,6,3],[4,6,8,3,1,7,5,2],[5,2,8,1,4,7,3,6],[7,1,3,8,6,4,2,5],[4,8,1,3,6,2,7,5],
        [4,7,3,8,2,5,1,6],[4,7,5,2,6,1,3,8],[4,8,1,5,7,2,6,3],[4,7,5,3,1,6,8,2],[5,3,1,6,8,2,4,7],
        [5,3,1,7,2,8,6,4],[4,8,5,3,1,7,2,6],[5,7,1,3,8,6,4,2],[5,7,1,4,2,8,6,3],[5,3,8,4,7,1,6,2],
        [6,2,7,1,3,5,8,4],[6,2,7,1,4,8,5,3],[5,7,2,4,8,1,3,6],[5,7,2,6,3,1,4,8],[5,7,2,6,3,1,8,4],
        [5,7,4,1,3,8,6,2],[6,3,1,8,4,2,7,5],[6,3,1,7,5,8,2,4],[6,3,1,8,5,2,4,7],[7,2,4,1,8,5,3,6],
        [5,8,4,1,3,6,2,7],[5,8,4,1,7,2,6,3],[6,3,5,7,1,4,2,8],[6,4,1,5,8,2,7,3],[6,3,5,8,1,4,2,7],
        [6,3,7,2,4,8,1,5],[6,3,7,2,8,5,1,4],[6,3,7,4,1,8,2,5],[7,2,6,3,1,4,8,5],[8,2,4,1,7,5,3,6],
        [6,4,7,1,3,5,2,8],[6,4,7,1,8,2,5,3],[6,4,2,8,5,7,1,3],[8,2,5,3,1,7,4,6],[7,3,1,6,8,5,2,4],
        [6,8,2,4,1,7,5,3],[8,3,1,6,2,5,7,4],[7,3,8,2,5,1,6,4],[8,4,1,3,6,2,7,5],[7,4,2,5,8,1,3,6],
        [7,4,2,8,6,1,3,5],[7,5,3,1,6,8,2,4]]
```

First, let us confirm in the repl that we get the same answer from both methods, as far as solving the n queens problem goes.

```haskell
>>> import Data.Set as Set
>>> Set.fromList (queens 8 (>>=) :: [Q]) == Set.fromList (observeAll (queens 8 (>>-) :: Logic Q))
True
```

As we expected, the logic monad traversed the search tree differently from the list monad. Looking at the output from the list monad, we can see that the solutions were produced in lexicographic order. This corresponds to the fact that the list monad traversed the search space using depth first traversal. See [here](http://cs.nyu.edu/courses/spring03/G22.2560-001/nondet.html) for a discussion of the search spaces associated to nondeterministic computations and the depth first traversal of those spaces.

Now, since the list monad traversal was so easy to understand, might we obtain a similarly simple description of the logic monad traveral? Not that I could tell.

I contented myself with the following diagrams (for n = 4, 5) of the traversal, made with [Diagrams](http://projects.haskell.org/diagrams/). Note that the trees shown in the figures are much larger than the search trees created by folding `awtaoq` n times.

TODO: add the diagrams.
