{-# LANGUAGE Rank2Types #-}

import Data.Maybe

newtype Church a = Church { runChurch :: forall r. (a -> r       -> r) -> r -> r }
newtype Scott  a = Scott  { runScott  :: forall r. (a -> Scott a -> r) -> r -> r }

----------

cnil :: Church a
cnil = Church $ \f z -> z

ccons :: a -> Church a -> Church a
ccons x xs = Church $ \f z -> f x (cfoldr f z xs)

cfoldr :: (a -> r -> r) -> r -> Church a -> r
cfoldr f z xs = runChurch xs f z

czipWith :: (a -> b -> c) -> Church a -> Church b -> Church c
czipWith f xs ys = fromScott $ szipWith f (fromChurch xs) (fromChurch ys)

----------

snil :: Scott a
snil = Scott $ \f z -> z

scons :: a -> Scott a -> Scott a
scons x xs = Scott $ \f z -> f x xs

sfoldr :: (a -> r -> r) -> r -> Scott a -> r
sfoldr f z xs = runScott xs (\x -> f x . sfoldr f z) z

----------

split :: Scott a -> Maybe (a, Scott a)
split xs = runScott xs ((Just .) . (,)) Nothing

szipWith :: (a -> b -> c) -> Scott a -> Scott b -> Scott c
szipWith f xs ys = fromMaybe snil $ do
	(x, xs') <- split xs
	(y, ys') <- split ys
	return $ f x y `scons` szipWith f xs' ys'

---------

fromChurch :: Church a -> Scott a
fromChurch = cfoldr scons snil

fromScott  :: Scott a  -> Church a
fromScott  = sfoldr ccons cnil

---------

cfromList :: [a] -> Church a
cfromList = foldr ccons cnil

ctoList :: Church a -> [a]
ctoList = cfoldr (:) []

sfromList :: [a] -> Scott a
sfromList = foldr scons snil

stoList :: Scott a -> [a]
stoList = sfoldr (:) []

main = print $ length $ ctoList $ czipWith (,) (cfromList [1..10^6]) (cfromList [1..10^6])
