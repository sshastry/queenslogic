
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Rank2Types #-}

import Diagrams.Prelude
import Diagrams.Backend.SVG.CmdLine
import Diagrams.TwoD.Layout.Tree
import Data.Maybe (fromMaybe)

import QueensLogic
import Control.Monad.Logic
import Data.List (intersect,inits,(\\))
import Data.Tree
import Data.Maybe (fromJust)

{- TODO: complete refactoring and rewrite -}

-- example = make fourP -- runghc illustrations.hs -o four.svg -w 5000 -h 1100
example = make fiveP -- runghc illustrations.hs -o five.svg -w 24000 -h 1250
-- example = make eightP -- runs out of memory
main = mainWith example

data Parameters = Parameters
    { size :: Int -- the size of the board
    , dv :: Double -- total vertical translation
    , dh :: Double -- total horiz translation
    , dhR :: Double -- horiz translation of the red paths
    , dhG :: Double -- horiz translation of the green paths
    , slHSep0 :: Double
    , slVSep0 :: Double
    , rrw :: Double
    , rrh :: Double
    , rrr :: Double
    , rrpad :: Double
    , dotsize :: Double
    , lwglobal :: Measure R2
    , glistv :: Double
    , glogicv :: Double
    }

fourP = Parameters
    { size = 4
    , dv = 13.0
    , dh = 0.0
    , dhR = -2.0
    , dhG = 2.0
    , slHSep0 = 6.0
    , slVSep0 = 6.0
    , rrw = 4.0
    , rrh = 2.0
    , rrr = 0.3
    , rrpad = 1.1
    , dotsize = 0.5
    , glistv = 10.0
    , glogicv = 8.0
    , lwglobal = veryThin
    }

fiveP = Parameters
    { size = 5
    , dv = 16.0
    , dh = 0.0
    , dhR = -2.0
    , dhG = 2.0
    , slHSep0 = 6.0
    , slVSep0 = 6.0
    , rrw = 4.0
    , rrh = 2.0
    , rrr = 0.3
    , rrpad = 1.1
    , dotsize = 0.5
    , glistv = 12.0
    , glogicv = 10.0
    , lwglobal = veryThin
    }

-- eightP = Parameters
--     { size = 8
--     , dv = 16.0
--     , dh = 0.0
--     , dhR = -2.0
--     , dhG = 2.0
--     , slHSep0 = 6.0
--     , slVSep0 = 6.0
--     , rrw = 4.0
--     , rrh = 2.0
--     , rrr = 0.3
--     , rrpad = 1.1
--     , dotsize = 0.5
--     , glistv = 12.0
--     , glogicv = 10.0
--     , lwglobal = veryThin
--     }

-- all ways to add one integer (which has not already been seen and is in the range [1..size])
awtaoi :: Int -> Q -> [Q]
awtaoi n xs = [xs ++ [j] | j <- [1..n] \\ xs]

f :: Int -> K [] Q -> (Q -> (Q, [Q]))
f n (>>~) = \xs -> (xs, [xs] >>~ (awtaoi n))

show0 :: [Int] -> String
show0 [] = "∅"
show0 xs = foldl1 (++) $ map show xs

makeBigTree :: Int -> Tree Q
makeBigTree n = unfoldTree (f n (>>=)) []

unrenderedTree :: Parameters -> Tree a -> (a -> String) -> Tree (String,P2)
unrenderedTree p t f = (symmLayout' (with & slHSep .~ sH & slVSep .~ sV) tree0)
  where
    sH = slHSep0 p
    sV = slVSep0 p
    tree0 = fmap f t

renderedTree :: Parameters -> Tree (String,P2) -> Diagram B R2
renderedTree p t = renderTree (rr . text) (~~) t # centerXY # pad px # lw lw0
  where
    (w,h,r,px) = (rrw p, rrh p, rrr p,rrpad p)
    lw0 = lwglobal p
    rr = (<> roundedRect w h r # fc gold # lw lw0)

get :: Eq a => a -> [(a, b)] -> b
get x h = fromJust (lookup x h)

numcircle :: Int -> Diagram B R2
numcircle n = text (show n) # fc white <> circle 0.5 # fc black

greennum :: Int -> Diagram B R2
greennum n = text (show n) # fc white <> circle 0.5 # fc black

nxs :: [a] -> [(Int,a)]
nxs xs = zip [1..n] xs where n = length xs

make :: Parameters -> Diagram B R2
make p = mconcat
    [ drawPartition
    , reT
    , listtxt
    , logictxt
    , greenlistnums
    , greenlogicnums ]
  where
    n = size p
    greenslist = queens n (>>=) :: [Q]
    listleaves = foldl (>>=) [[]] (replicate n (awtaoi n))
    redslist = listleaves \\ greenslist
    greenslogic = queens n (>>-) :: [Q]
    logicleaves = foldl (>>-) [[]] (replicate n (awtaoi n))
    redslogic = logicleaves \\ greenslogic
    bigtree = makeBigTree n
    unT = unrenderedTree p bigtree show0
    reT = renderedTree p unT
    leaves = last . levels
    leafstrs = map show0 (leaves bigtree)
    paths = map inits (leaves bigtree)
    strPaths = (fmap.fmap) show0 paths
    leafstrToPathHash :: [(String,[P2])]
    leafstrToPathHash = [(l,g l) | l <- leafstrs]
      where
        strToPointHash = flatten unT
        strToCleanedKeys s = map (\s0 -> if s0 == "" then "∅" else s0) (inits s)
        g l = map (\s -> get s strToPointHash) (strToCleanedKeys l)
    drawPartition :: Diagram B R2
    drawPartition = mconcat ([drawPath s lawngreen hG | s <- gs] ++ [drawPath s red hR | s <- rs])
      where
        gs = fmap show0 greenslogic
        rs = fmap show0 redslogic
        (h,v,hG,hR,lw0) = (dh p,dv p,dhG p,dhR p,lwglobal p)
        path s = get s leafstrToPathHash
        drawPath :: String -> Colour Double -> Double -> Diagram B R2
        drawPath s col h' = (reV (path s) h' col) <> (stroke $ fromVertices $ map (translate (r2 (h',v))) (path s)) # lc col # lw lw0
          where
            reV :: [P2] -> Double -> Colour Double -> Diagram B R2
            reV ps h' col = mconcat $ map (\p -> translate (r2 (h',v)) dot # moveTo p) $ ps
              where
                dot = circle (dotsize p) # fc col # lw none
    leafpts :: [(String, P2)]
    leafpts = map (\(s,ps) -> (s,last ps)) leafstrToPathHash
    leafptsOrd :: [String] -> [(Int, P2)]
    leafptsOrd ss = map (\(i,s) -> (i,(get s leafpts))) (nxs ss)
    drawnums :: [(Int, P2)] -> Double -> Diagram B R2
    drawnums ls dv = mconcat $
        map (\(n,p) -> translate (r2 (0,dv)) (numcircle n) # moveTo p) ls
    drawgreennums :: [String] -> (Double,Double) -> Diagram B R2
    drawgreennums ls (dh,dv) = drawnums' (leafptsOrd ls)
      where
        drawnums' :: [(Int, P2)] -> Diagram B R2
        drawnums' xs = mconcat $
            map (\(n,p) -> translate (r2 (dh,dv)) (greennum n) # moveTo p) xs
    greenlistnums :: Diagram B R2
    greenlistnums = drawgreennums (map show0 greenslist) (0,glistv p)
    greenlogicnums :: Diagram B R2
    greenlogicnums = drawgreennums (map show0 greenslogic) (0,glogicv p)
    listtxt :: Diagram B R2
    listtxt = txt
      where
        ls = leafptsOrd (map show0 listleaves)
        p0 = snd (head ls)
        txt = translate (r2 (-6.0,glistv p)) $ text "List" # moveTo p0
    logictxt :: Diagram B R2
    logictxt = txt
      where
        ls = leafptsOrd (map show0 logicleaves)
        p0 = snd (head ls)
        txt = translate (r2 (-6.0,glogicv p)) $ text "Logic" # moveTo p0

