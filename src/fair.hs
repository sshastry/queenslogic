
import Control.Monad.Logic

odds :: [Int]
odds = map (\x -> 2*x + 1) [0..]

ts :: [Int]
ts = [10] ++ [20] ++ [30]

z :: Int
z = head $ (odds ++ ts) >>= (\x -> if even x then [x] else [])

choices :: MonadLogic m => [a] -> m a
choices = msum . map return

odds' :: Logic Int
odds' = choices odds

ts' :: Logic Int
ts' = choices [10,20,30]

z' :: Int
z' = observe $ (odds' `interleave` ts') >>= (\x -> if even x then return x else mzero)

oddsPlus :: Int -> [Int]
oddsPlus n = odds >>= \x -> return (x + n)

xs :: [Int]
xs = ([0] ++ [1]) >>= oddsPlus >>= (\x -> if even x then [x] else [])

oddsPlus' :: Int -> Logic Int
oddsPlus' n = odds' >>= \x -> return (x + n)

xs' :: Logic Int
xs' = ((return 0) `interleave` (return 1)) >>= oddsPlus' >>= (\x -> if even x then (return x) else mzero)

xs'' :: Logic Int
xs'' = ((return 0) `interleave` (return 1)) >>- oddsPlus' >>- (\x -> if even x then (return x) else mzero)




