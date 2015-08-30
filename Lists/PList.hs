{-# LANGUAGE Rank2Types #-}

import Data.Maybe
import Data.List

newtype PList a = PList { runPList :: forall r. (PList a -> a -> r -> r) -> r -> r }

pnil :: PList a
pnil = PList $ \_ z -> z

pcons :: a -> PList a -> PList a
pcons x xs = PList $ \f z -> f xs x (runPList xs f z)

psplit :: PList a -> Maybe (a, PList a)
psplit xs = runPList xs (\t h _ -> Just (h, t)) Nothing

pfoldr :: (a -> r -> r) -> r -> PList a -> r
pfoldr f z xs = runPList xs (\_ -> f) z

pfuse :: PList a -> PList a
pfuse = pfoldr pcons pnil

pappend :: PList a -> PList a -> PList a
pappend xs ys = PList $ \f -> runPList xs (\xs' -> f (pappend xs' ys)) . runPList ys f

pmap :: (a -> b) -> PList a -> PList b
pmap h xs = PList $ \f -> runPList xs (\xs' -> f (pmap h xs') . h)

pzipWith :: (a -> b -> c) -> PList a -> PList b -> PList c
pzipWith f xs ys = go (pfuse xs) (pfuse ys) where
	go xs ys = fromMaybe pnil $ do
		(x, xs') <- psplit xs
		(y, ys') <- psplit ys
		return $ f x y `pcons` go xs' ys'

pzip :: PList a -> PList b -> PList (a, b)
pzip = pzipWith (,)

pfromList :: [a] -> PList a
pfromList = foldr pcons pnil

ptoList :: PList a -> [a]
ptoList = pfoldr (:) []

main = do
	print $ ptoList $ pzip (pfromList [1..10]) (pfromList [1..10])
-- [(1,1),(2,2),(3,3),(4,4),(5,5),(6,6),(7,7),(8,8),(9,9),(10,10)]
	print $ ptoList $ pzip (pfromList [1..10]) (pfromList [1..9 ])
-- [(1,1),(2,2),(3,3),(4,4),(5,5),(6,6),(7,7),(8,8),(9,9)]	
	print $ ptoList $ pzip (pfromList [1..9 ]) (pfromList [1..10])
-- [(1,1),(2,2),(3,3),(4,4),(5,5),(6,6),(7,7),(8,8),(9,9)]
	print $ length . ptoList $ foldl' pappend pnil . map (pfromList . (:[])) $ [1..1000000]
-- 1000000