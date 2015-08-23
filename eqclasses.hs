import Data.List

set :: Int -> a -> [a] -> [a]
set 0 y (x:xs) = y : xs
set n y (x:xs) = x : set (n - 1) y xs

sets :: [Int] -> a -> [a] -> [a]
sets is x xs = foldr (flip set x) xs is

eqclasses :: [(Int, Int)] -> [[Int]]
eqclasses ps = nub $ go ps (map (:[]) [0 .. maximum $ ps >>= \(x, y) -> [x, y]]) where 
	go :: [(Int, Int)] -> [[Int]] -> [[Int]]
	go  []         cs = cs
	go ((i, j):ps) cs = go ps $
		if i `elem` cs !! j
			then cs
			else let ks = (cs !! i) ++ (cs !! j) in sets ks ks cs