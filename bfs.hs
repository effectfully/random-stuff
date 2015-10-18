data Tree a = Leaf a | Node a (Tree a) (Tree a)

data Shift a = None | Some a | Shift (Shift a)
newtype Crescendo a = Crescendo (Shift (a, Crescendo a))

shift :: Crescendo a -> Crescendo a
shift (Crescendo c) = Crescendo (Shift c)

fromCrescendo :: Crescendo a -> [a]
fromCrescendo (Crescendo s) = fromShift s

fromShift :: Shift (a, Crescendo a) -> [a]
fromShift  None         = []
fromShift (Some (x, c)) = x : fromCrescendo c
fromShift (Shift s)     = fromShift s

mergeCrescendo :: Crescendo a -> Crescendo a -> Crescendo a
mergeCrescendo (Crescendo s1) (Crescendo s2) = Crescendo (mergeShift s1 s2)

mergeShift :: Shift (a, Crescendo a) -> Shift (a, Crescendo a) -> Shift (a, Crescendo a)
mergeShift  None           s2            = s2
mergeShift  s1             None          = s1
mergeShift (Some (x, c1))  s2            = Some (x, mergeCrescendo c1 (Crescendo s2))
mergeShift  s1            (Some (x, c2)) = Some (x, mergeCrescendo (Crescendo s1) c2)
mergeShift (Shift s1)     (Shift s2)     = Shift (mergeShift s1 s2)

ifSome :: (a -> Bool) -> a -> Crescendo a -> Crescendo a
ifSome p x c
	| p x       = Crescendo (Some (x, c))
	| otherwise = c

cbfs :: (a -> Bool) -> Tree a -> Crescendo a
cbfs p (Leaf x)     = ifSome p x (Crescendo None)
cbfs p (Node x l r) = ifSome p x (shift (mergeCrescendo (cbfs p l) (cbfs p r)))

bfs :: (a -> Bool) -> Tree a -> [a]
bfs p t = fromCrescendo (cbfs p t)
