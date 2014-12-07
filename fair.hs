
import Control.Monad.Logic

odds :: [Integer]
odds = [1] ++ (odds >>= \x -> [x+2])

ts :: [Integer]
ts = [10] ++ [20] ++ [30]

z :: Integer
z = head $ (odds ++ ts) >>= (\x -> if even x then [x] else [])

odds0 :: Logic Integer
odds0 = (return 1) `mplus` (odds0 >>= \x -> return (x+2))

ts0 :: Logic Integer
ts0 = msum (map return [10,20,30])

z0 :: Integer
z0 = observe $ (odds0 `interleave` ts0) >>= (\x -> if even x then return x else mzero)

