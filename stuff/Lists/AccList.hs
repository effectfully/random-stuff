-- totally isomorphic to [], even in a strict monad
-- no redundant (<= 0) checks in the `drop' function
-- the `zipWith' function is still O(n^2)

{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE BangPatterns #-}

import Data.List
import Control.Applicative
import Control.Monad
import Control.Arrow

_u = id

dup x = (x, x)

infixr 9 .*
(.*) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(.*) = (.) . (.)

(!-) :: Integer -> Integer -> Integer
n !- m = let d = n - m in if d <= 0 then 0 else d

addToAcc x (acc, res) = ((acc, x), res)

infixr 5 $: , $++
infixr 9 $!!

newtype AccList a = AccList {runAccList :: forall b c.
	Integer -> c -> b -> (c -> a -> (c, b -> b)) -> b
}

instance Functor AccList where
	fmap f xs = pure f <*> xs

instance Applicative AccList where
	pure  = return
	(<*>) = ap

instance Monad AccList where
	return = ($: nil)
	(>>=)  = flip fconcatMap

nil :: AccList a
nil = AccList $ \_ _ res _ -> res

($:) :: a -> AccList a -> AccList a
x $: xs = AccList $ \d acc res facc -> if d == 0
	then let (acc', fres) = facc acc x in
		fres $ runAccList xs 0 acc' res facc
	else runAccList xs (d - 1) acc res facc

runAccListAccEnd :: AccList a -> forall b c.
	Integer -> c -> (c -> (c, b)) -> (c -> a -> (c, b -> b)) -> (c, b)
runAccListAccEnd xs d acc end facc = ($ acc) $ runAccList xs d acc end $
	\(!acc') x -> let (acc'', fres) = facc acc' x in (,) acc'' $
		\end' -> let (acc''', res') = end' acc'' in
			const (acc''', fres res')

runAccListAcc :: AccList a -> forall b c.
	Integer -> c -> b -> (c -> a -> (c, b -> b)) -> (c, b)
runAccListAcc xs d acc res facc =
	runAccListAccEnd xs d acc (flip (,) res) facc

runAccListEnd :: AccList a -> forall b c.
	Integer -> c -> (c -> b) -> (c -> a -> (c, b -> b)) -> b
runAccListEnd xs d acc end facc =
	snd $ runAccListAccEnd xs d acc (second end . dup) facc

ffromList = foldr ($:) nil
ftoList   = ffoldr (:) []

-- Basic functions.

($++) :: AccList a -> AccList a -> AccList a
xs $++ ys = AccList $ \d acc res facc ->
	let (acc', res') = runAccListAcc xs d acc
		(runAccList ys (d !- flength xs) acc' res facc) facc
	in res'

fhead :: AccList a -> a
fhead = ffoldr const (error "empty list")

-- flast

ftail :: AccList a -> AccList a
ftail = fdrop 1

-- finit

fnull :: AccList a -> Bool
fnull = ffoldr (\_ _ -> True) False

flength :: AccList a -> Integer
flength = ffoldl' (\r _ -> r + 1) 0

-- List transformations

ffmap :: (a -> b) -> AccList a -> AccList b
ffmap f xs = AccList $ \d acc res facc ->
	runAccList xs d acc res $ \acc' -> facc acc' . f

freverse :: AccList a -> AccList a
freverse = ffoldl (flip ($:)) nil

-- fintersperse

-- fintercalate

-- ftranspose

fsubsequences :: AccList a -> AccList (AccList a)
fsubsequences = (nil $:) . f (\x -> (pure x $:) . f (\ys r -> ys $: (x $: ys) $: r))
	where f = flip ffoldr nil

-- fpermutations

-- Reducing lists (folds) 

ffoldl :: (b -> a -> b) -> b -> AccList a -> b
ffoldl f z xs = fst $ runAccListAcc xs 0 z () $ \res' x -> (f res' x, id)

ffoldl' :: (b -> a -> b) -> b -> AccList a -> b
ffoldl' f z xs = fst $ runAccListAcc xs 0 z () $ \(!res') x -> (f res' x, id)

-- ffoldl1

-- ffoldl1'

ffoldr :: (a -> b -> b) -> b -> AccList a -> b
ffoldr f z xs = runAccList xs 0 () z (\() x -> ((), f x))

-- Special folds 

fconcat :: AccList (AccList a) -> AccList a
fconcat = ffoldr ($++) nil

fconcatMap :: (a -> AccList b) -> AccList a -> AccList b
fconcatMap = fconcat .* ffmap

fand :: AccList Bool -> Bool
fand = fall id

for :: AccList Bool -> Bool
for = fany id

fany :: (a -> Bool) -> AccList a -> Bool
fany p = ffoldr ((||) . p) False

fall :: (a -> Bool) -> AccList a -> Bool
fall p = ffoldr ((&&) . p) True

fsum :: Num a => AccList a -> a
fsum = ffoldl' (+) 0

fproduct :: Num a => AccList a -> a
fproduct = ffoldl' (*) 1

-- fmaximum

-- fminimum

-- Building lists

-- Scans

fscanl :: (b -> a -> b) -> b -> AccList a -> AccList b
fscanl f z xs = AccList $ \d acc res facc ->
	let (z', _) = runAccListAcc (ftake d xs) 0 z res
		(\z'' x -> (f z'' x, _u))
	in runAccListEnd xs d (acc, z')
		(\(acc', z'') -> ($ res) $ snd $ facc acc' z'')
		(\(acc', z'') x -> addToAcc (f z'' x) $ facc acc' z'')
		
-- fscanl1

fscanr :: (a -> b -> b) -> b -> AccList a -> AccList b
fscanr f = uncurry ($:) .* fmapAccumR (dup .* flip f)

-- fscanr1

-- Accumulating maps

fmapAccumL :: (c -> a -> (c, b)) -> c -> AccList a -> (c, AccList b)
fmapAccumL f z xs = runAccListAcc xs 0 z nil $ second ($:) .* f

fsndMapAccumL :: (c -> a -> (c, b)) -> c -> AccList a -> AccList b
fsndMapAccumL f z xs = AccList $ \d acc res facc ->
	let (z', _) = runAccListAcc (ftake d xs) 0 z res $
		\z'' x -> (fst $ f z'' x, _u)
	in runAccList xs d (acc, z') res $
		\(acc', z'') x -> let (z''', x') = f z'' x in
			addToAcc z''' $ facc acc' x'

fmapAccumR :: (c -> a -> (c, b)) -> c -> AccList a -> (c, AccList b)
fmapAccumR f z = ffoldr (\x (z', xs') -> ($: xs') `second` f z' x) (z, nil)

-- Infinite lists

frepeat :: a -> AccList a
frepeat = ffromList . repeat

fiterate :: (a -> a) -> a -> AccList a
fiterate = ffromList .* iterate

freplicate :: Integer -> a -> AccList a
freplicate n = ftake n . frepeat

fcycle :: AccList a -> AccList a
fcycle xs | fnull xs = error "Empty list"
fcycle xs = xs' where xs' = xs $++ xs'

-- Unfolding

funfoldr :: (b -> Maybe (a, b)) -> b -> AccList a
funfoldr = ffromList .* unfoldr

-- Sublists

-- Extracting sublists

ftake :: Integer -> AccList a -> AccList a
ftake n xs = AccList $ \d acc res facc ->
	runAccList xs d (acc, n - d) res $
		\(acc', n') x -> if n' <= 0
			then ((acc', 0), const res)
			else addToAcc (n' - 1) $ facc acc' x

fdrop :: Integer -> AccList a -> AccList a
fdrop n xs = AccList $ \d -> runAccList xs (d + n)

fsplitAt :: Integer -> AccList  a -> (AccList  a, AccList  a)
fsplitAt n xs = (ftake n xs, fdrop n xs)
 
ftakeWhile :: (a -> Bool) -> AccList  a -> AccList  a
ftakeWhile p xs = AccList $ \d acc res facc ->
	if fall p (ftake d xs)
		then runAccList xs d acc res $
			\acc' x -> if p x then facc acc' x else (acc', const res)
		else res
 
fdropWhile :: (a -> Bool) -> AccList  a -> AccList  a
fdropWhile p xs = AccList $ \d ->
	runAccList xs (d + flength (ftakeWhile p xs))

-- fdropWhileEnd

fspan :: (a -> Bool) -> AccList a -> (AccList a, AccList a)
fspan p xs = (ftakeWhile p xs, fdropWhile p xs) 

fbreak :: (a -> Bool) -> AccList a -> (AccList a, AccList a)
fbreak p = fspan (not . p)

-- fstripPrefix

-- fgroup

finits :: AccList a -> AccList (AccList a)
finits xs = ffoldr (\x r -> nil $: fmap (x $:) r) (nil $: nil) xs

ftails :: AccList a -> AccList (AccList a)
ftails xs = fscanl (\xs' _ -> ftail xs') xs xs

-- Predicates

-- fisPrefixOf

-- fisSuffixOf

-- fisInfixOf

-- Searching lists

-- Searching by equality

felem :: Eq a => a -> AccList a -> Bool
felem = fany . (==)

fnotElem :: Eq a => a -> AccList a -> Bool
fnotElem = fall . (/=)

flookup :: Eq a => a -> AccList (a, b) -> Maybe b
flookup k = ffoldr (\(k', x) r -> if k == k' then Just x else r) Nothing

-- Searching with a predicate

ffind :: (a -> Bool) -> AccList a -> Maybe a
ffind = flistToMaybe .* ffilter

ffilter :: (a -> Bool) -> AccList a -> AccList a
ffilter p xs = AccList $ \d acc res facc -> runAccList xs d acc res $
	\acc' x -> if p x then facc acc' x else (acc', id)

fpartition :: (a -> Bool) -> AccList a -> (AccList a, AccList a)
fpartition p xs = (ffilter p xs, ffilter (not . p) xs) 

-- fIndexing lists

($!!) :: AccList a -> Integer -> a 
xs $!! n = fhead $ fdrop n xs

felemIndex :: Eq a => a -> AccList a -> Maybe Integer
felemIndex = ffindIndex . (==)

felemIndices :: Eq a => a -> AccList a -> AccList Integer
felemIndices = ffindIndices . (==)

ffindIndex :: (a -> Bool) -> AccList a -> Maybe Integer
ffindIndex = flistToMaybe .* ffindIndices

ffindIndices :: (a -> Bool) -> AccList a -> AccList Integer
ffindIndices p xs = AccList $ \d acc res facc ->
	let ((_, d'), _) = runAccListAcc xs 0 (d, 0) res $
		\(d', n') x -> if d' == 0
			then ((0, n'), _u)
			else ((if p x then d' - 1 else d', n' + 1), _u)
	in runAccList xs d' (acc, d') res $
		\(acc', n'') x -> if p x
			then addToAcc (n'' + 1) $ facc acc' n''
			else ((acc', n'' + 1), id)

-- Maybe

flistToMaybe :: AccList a -> Maybe a
flistToMaybe = ffoldr (\x _ -> Just x) Nothing

main = do
	print $ drop 2 $ findIndices even [1..15]
	print $ ftoList $ fdrop 2 $ ffindIndices even $ ffromList [1..15]

	print $ take 10 $ drop 5 $ take 20 $ take 27 $ findIndices even $ drop 5 $ scanl (-) 2 $ take 40 $ drop 10 [1..]
	print $ ftoList $ ftake 10 $ fdrop 5 $ ftake 20 $ ftake 27 $ ffindIndices even $ fdrop 5 $ fscanl (-) 2 $ ftake 40 $ fdrop 10 $ ffromList [1..]

	print $ reverse $ take 10 $ drop 3 $ reverse $ take 28 $ filter even $ drop 5 $ snd $ mapAccumL (\x y -> (x+y, x*y)) 5 $ takeWhile (<= 30) $ take 40 $ drop 10 [1..] 
	print $ ftoList $ freverse $ ftake 10 $ fdrop 3 $ freverse $ ftake 28 $ ffilter even $ fdrop 5 $ fsndMapAccumL (\x y -> (x+y, x*y)) 5 $ ftakeWhile (<= 30) $ ftake 40 $ fdrop 10 $ ffromList [1..]
