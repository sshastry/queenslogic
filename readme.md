
## Introduction

The aim of these notes is to apply the logic monad to the n queens problem. The logic monad was introduced in paper "Backtracking, interleaving, and terminating monad transformers: (functional pearl)" by Oleg Kiselyov, Chung-chieh Shan, Daniel P. Friedman, Amr Sabry (henceforth [KSFS]; paper available [here](http://okmij.org/ftp/papers/LogicT.pdf)). Also see "Adventures in Three Monads" by Edward Z. Yang in [The Monad Reader Issue 15](http://themonadreader.files.wordpress.com/2010/01/issue15.pdf).

The first backtracking algorithm I learned was the solution to the n queens problem, so I wondered what I could see by solving it with the logic monad.

## Logic

Besides being used for collections, the list type Haskell is used to represent a nondeterministic value. For example `xs :: [Int]` might mean a finite or countably infinite sequence of integers, or it might mean one of many unknown integers i.e. a single nondeterministic integer. The latter semantics is illustrated by the following

```haskell
>>> fmap (\x -> x*x) [1,2,3]
[1,4,9]
```

which we take to mean
> if we square a value which may be 1, 2, or 3 we get a value which may be 1, 4, or 9.

Now, we are not only interested in assembling nondeterministic values monadically i.e. with `(>>=)` (where, in the above example, `fmap f x = x >>= (return . f)`) we are also interested in assembling them with another operation `mplus`, which in the case of the MonadPlus instance on list is `(++)`. For example:

```haskell
>>> fmap (\x -> x*x) ([2,4] ++ [10,20])
[4,16,100,400]
```

in other words `mplus` allows us to build up new nondeterministic values from old. Thus MonadPlus allows us to build up computations in two distinct ways: monadically and with `mplus`. For reference, here's the MonadPlus typeclass and instance on list:

```haskell
class Monad m => MonadPlus m where
  mzero :: m a
  mplus :: m a -> m a -> m a

instance MonadPlus [] where
  mzero = []
  mplus = (++)
```

Some laws should be satisfied for a type to be called a MonadPlus (see [here](http://hackage.haskell.org/package/base-4.7.0.2/docs/src/Control-Monad.html#MonadPlus)).

Naively building up a nondeterministic value using `(++)` with list as MonadPlus, we might encounter the following problem (example taken from [KSFS]):

```haskell
>>> let odds = map (\x -> 2*x + 1) [0..]
>>> head $ filter even (odds ++ [10,20,30])
^CInterrupted.
```

i.e. ghci hangs and we had to ctrl-c out of it. Let's make very explicit the operations of list as MonadPlus:

```haskell
odds :: [Int]
odds = map (\x -> 2*x + 1) [0..]

ts :: [Int]
ts = [10] ++ [20] ++ [30]

z :: Int
z = head $ (odds ++ ts) >>= (\x -> if even x then [x] else [])
```

As before, if we were to try to evaluate `z` in the repl, ghci would hang. This is unfortunate, since z should be equal to 10, the first even number in the list `odds ++ ts`. The problem is that `(++)` is *unfair* in the sense that it demands that all of the elements of its first argument be shoved through the `(>>=)` before its second argument gets a chance. The logic monad provides a fair version of `mplus`, called `interleave`, such that (xs `interleave` ys) will shove the first element of `xs` through `(>>=)`, then the first element of `ys`, then the second element of `xs`, then the second element of `ys`, etc.

```haskell
import Control.Monad.Logic

choices :: MonadLogic m => [a] -> m a
choices = msum . map return

odds' :: Logic Int
odds' = choices odds

ts' :: Logic Int
ts' = choices [10,20,30]

z' :: Int
z' = observe $ (odds' `interleave` ts') >>= (\x -> if even x then return x else mzero)
```

In the repl:

```haskell
>>> z'
10
```

Given two nondeterministic values `x` and `y` (in some monadic context of nondeterminism) let's define `x ≃ y` to mean that the set of values emitted by `x` and `y` are the same --- so that the order in which the elements appear is ignored --- and otherwise we write `x ≄  y`. If `x` is an infinite list then we have that `x ++ y ≃ x` i.e. we can only observe elements of `x`. So `≃` and `≄` give us a more precise way to talk about the fairness of computations.

Now, the unfairness of `mplus` leads to the unfairness of `(>>=)`: if `x` is infinite then we have that `(x ++ y >>= k) ≃ (x >>= k)`, something we saw in the earlier example. But `x` being infinite is not the only way that `x ++ y >>= k` could fail, as shown by the following example (also from [KSFS]):

```haskell
oddsPlus :: Int -> [Int]
oddsPlus n = odds >>= \x -> return (x + n)

xs :: [Int]
xs = ([0] ++ [1]) >>= oddsPlus >>= (\x -> if even x then [x] else [])
```

In the repl, evaluating `xs` hangs since the fragment `(\x -> if even x then [x] else [])` backtracks to `oddsPlus` an infinite number of times, even though we know that the first element of `xs` should be 2. Replacing `(++)` with `interleave` does us no good, evaluating `xs'` below will also hang:

```haskell
oddsPlus' :: Int -> Logic Int
oddsPlus' n = odds' >>= \x -> return (x + n)

xs' :: Logic Int
xs' = ((return 0) `interleave` (return 1))
      >>= oddsPlus'
      >>= (\x -> if even x then (return x) else mzero)
```

We need a fair version of `(>>=)`, which is denoted `(>>-)`.

```haskell
xs'' :: Logic Int
xs'' = ((return 0) `interleave` (return 1))
       >>- oddsPlus'
       >>- (\x -> if even x then (return x) else mzero)
```

Then, in the repl:

```haskell
>>> head xs
^CInterrupted.
>>> observe xs'
^CInterrupted.
>>> observe xs''
2
```

## n queens

The problem is described [here](http://en.wikipedia.org/wiki/Eight_queens_puzzle). There is a solution to this problem in Haskell using list comprehensions [here](https://www.haskell.org/haskellwiki/99_questions/Solutions/90). That solution makes use of `[[Int]]` to represent a nondeterministic value of a collection of integers, thus using the list type with two different meanings. Let's tease apart the two meanings so that we can use the same code with both the list and logic monads.

Starting from scratch:

```haskell
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

-- K is for Kleisli
type K m a = Monad m => (m a -> (a -> m a) -> m a)
```

Now to the problem at hand. We index rows, columns, and diagonals by integers. The terminology is a little unorthodox in that we regard rows and columns as degenerate diagonals.

```haskell
data Diagonal = Row Int
              | Col Int
              | Backslash Int
              | Forwardslash Int
              deriving (Eq, Show)
```

Given a position `(i,j)` on the board, we send it to the list `[Row r, Col c, Backslash b, Forwardslash f]` containing it. We have chosen the numbering of diagonals so that there is no need to pass in the global board size. Note that the type Queens is meant to be a collection (not a nondeterministic value) of integers, such that the ith element of the list is j iff there is a queen at position `(i,j)`.

```haskell
type Square = (Int,Int)
type Queens = [Int] -- a configuration of nonattacking queens on the board
type Q = Queens

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

The following function is the inductive step of the algorithm. Given an admissible placement `qs` of queens, where the length of `qs` is strictly less than the dimension `n` of the board, `awtaoq` returns a nondeterministic value of all of the ways to extend `qs` by one more queen and still have an admissible placement of queens on the board. We enforce our chosen notion of nondeterminism by means of a [monad comprehension](https://ghc.haskell.org/trac/ghc/wiki/MonadComprehensions).

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
queens n (>>~) = foldl (>>~) (return mzero) (replicate n (awtaoq n))
```

Let's see how the two monads traverse the search space. Here's how list traverses with `(>>=)` (output formatted for readability):

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

First, let us confirm in the repl that we get the same answer from both methods, as far as solving the n queens problem goes. Also as a sanity check, let's make sure that we got 92 solutions to the 8 queens problem.

```haskell
>>> import Data.Set as Set
>>> Set.fromList (queens 8 (>>=) :: [Q]) == Set.fromList (observeAll (queens 8 (>>-) :: Logic Q))
True
>>> length (queens 8 (>>=) :: [Q])
92
```

As expected, the logic monad traversed the search space differently from the list monad. Looking at the output from the list monad, we can see that the solutions were produced in lexicographic order. This corresponds to the fact that the list monad traversed the search space using depth first traversal. See [here](http://cs.nyu.edu/courses/spring03/G22.2560-001/nondet.html) for a discussion of the search spaces associated to nondeterministic algorithms.

Now, since the list monad traversal was so easy to understand, might we obtain a similarly simple description of the logic monad traveral? Not that I could tell.

I contented myself with the following diagrams (for n = 4, 5) of the traversal, made with [Diagrams](http://projects.haskell.org/diagrams/). Note that the trees shown in the figures are much larger than the search trees created by folding `awtaoq` n times, since the search tree is being pruned by the algorithm as it goes (depending on which of `(>>=)` or `(>>-)` we use).

![four](https://raw.githubusercontent.com/sshastry/queenslogic/master/resources/four.png)

![five](https://raw.githubusercontent.com/sshastry/queenslogic/master/resources/five.png)

(click on the images and zoom in)

The green paths represent successful placements of n queens, which is to say, successful searches from the root to a leaf. The red paths are where the algorithm gave up at some point and backtracked. Given a red leaf, the precise point where the backtracking occurred was that unique ancestor of the red leaf which has no green path through it; those are the nodes at which the algorithm has determined that there is no way to add one more non-attacking queen.

The numbers in black along the bottom correspond to the order in which solutions were emitted by the list and logic monads, respectively. In the 5x5 diagram of the search tree we can see the logic monad working differently from list, for instance `[1,4,2,5,3]` is a correct solution to the five queens problem which is the third solution emitted by logic but is actually the second solution in the lexicographic order on lists of integers of length 5.

## The MonadLogic instance on List

It turns out that we don't need actually need to use the logic monad to observe all of the above, we can use the `MonadLogic` instance on list, which gives rise to `interleave` and `(>>-)` for lists.

```
>>> (queens 8 (>>-) :: [Q]) == observeAll (queens 8 (>>-) :: Logic Q)
True
```

The above says that using the MonadLogic instance on `[Q]` and using fair conjunction `(>>-)` to compute the solutions to the 8 queens problem emits solutions in the same order as if we used fair conjunction with `Logic Q`. So to get a better grasp on the logic monad, we can start by looking at the definition of the MonadLogic typeclass in [Control.Monad.Logic](http://hackage.haskell.org/package/logict-0.2.3/docs/src/Control-Monad-Logic-Class.html#MonadLogic) and then reflecting on this:

```haskell
-- An instance of MonadLogic for lists
instance MonadLogic [] where
    msplit []     = return Nothing
    msplit (x:xs) = return $ Just (x, xs)
```
