{-# LANGUAGE KindSignatures, ScopedTypeVariables, RankNTypes, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, TypeFamilies #-}

import Prelude
import Data.Proxy
import Data.Functor.Identity
import Data.Biapplicative

fst3 (x, y, z) = x
snd3 (x, y, z) = y
thd3 (x, y, z) = z

newtype S g f a = S { getS :: g a (f a) }

class Biapplicative (Layer f) => Split f where
  data Layer f a b
  
  split :: f a -> Layer f a (f a)
  unite :: Layer f a (f a) -> f a

class Tuple t where
  type Map (f :: * -> *) t

  outMap :: Biapplicative g => Proxy (f t) -> Map (S g f) t -> g t (Map f t)
  inMap  :: Biapplicative g => Proxy (f t) -> g t (Map f t) -> Map (S g f) t
  mapMap :: Proxy (f (g t)) -> (forall a. f a -> g a) -> Map f t -> Map g t

splitMap :: forall f t. (Split f, Tuple t) => Map f t -> Layer f t (Map f t)
splitMap = outMap (Proxy :: Proxy (f t))
         . mapMap (Proxy :: Proxy (f (S (Layer f) f t))) (S . split)

uniteMap :: forall f t. (Split f, Tuple t) => Layer f t (Map f t) -> Map f t
uniteMap = mapMap (Proxy :: Proxy (S (Layer f) f (f t))) (unite . getS)
         . inMap (Proxy :: Proxy (f t))

instance Tuple () where
  type Map f () = ()

  outMap _ () = bipure () ()
  inMap  _ _ = ()
  mapMap _ _ _ = ()

instance Tuple (Identity a) where
  type Map f (Identity a) = Identity (f a)

  outMap _ (Identity (S xs)) = bimap Identity Identity xs
  inMap  _ p = Identity (S (bimap runIdentity runIdentity p))
  mapMap _ n (Identity xs) = Identity (n xs)
  
instance Tuple (a, b) where
  type Map f (a, b) = (f a, f b)

  outMap _ (S xs, S ys) = biliftA2 (,) (,) xs ys
  inMap  _ p = (S (bimap fst fst p), S (bimap snd snd p))
  mapMap _ n (xs, ys) = (n xs, n ys)

instance Tuple (a, b, c) where
  type Map f (a, b, c) = (f a, f b, f c)

  outMap _ (S xs, S ys, S zs) = biliftA3 (,,) (,,) xs ys zs
  inMap _  p = (S (bimap fst3 fst3 p), S (bimap snd3 snd3 p), S (bimap thd3 thd3 p))
  mapMap _ n (xs, ys, zs) = (n xs, n ys, n zs)

gunzip :: (Split f, Tuple t) => f t -> Map f t
gunzip = uniteMap . second gunzip . split

gzip :: (Split f, Tuple t) => Map f t -> f t
gzip = unite . second gzip . splitMap

data Rose a = Rose a [Rose a] deriving (Show)
data Stream a = Stream a (Stream a)

type ListF   = Layer []
type RoseF   = Layer Rose
type StreamF = Layer Stream
  
instance Bifunctor ListF where
  bimap f g (ListF a) = ListF $ bimap f g <$> a

instance Bifunctor RoseF where
  bimap f g (RoseF x xs) = RoseF (f x) (map g xs)

instance Bifunctor StreamF where
  bimap f g (StreamF x y) = StreamF (f x) (g y)

instance Biapplicative ListF where
  bipure x y = ListF $ Just (x, y)
  ListF f <<*>> ListF a = ListF $ uncurry bimap <$> f <*> a

instance Biapplicative RoseF where
  bipure x y = RoseF x (repeat y)
  RoseF f fs <<*>> RoseF x xs = RoseF (f x) (zipWith id fs xs)

instance Biapplicative StreamF where
  bipure = StreamF
  StreamF f g <<*>> StreamF x y = StreamF (f x) (g y)

instance Split [] where
  data Layer [] a b = ListF (Maybe (a, b))
  
  split  []    = ListF Nothing
  split (x:xs) = bipure x xs

  unite (ListF  Nothing)       = []
  unite (ListF (Just (x, xs))) = x:xs

instance Split Rose where
  data Layer Rose a b = RoseF a [b]
  
  split (Rose  x xs) = RoseF x xs
  
  unite (RoseF x xs) = Rose  x xs

instance Split Stream where
  data Layer Stream a b = StreamF a b

  split (Stream  x xs) = StreamF x xs

  unite (StreamF x xs) = Stream  x xs

-- [(1,4,7),(2,5,8),(3,6,9)]
-- ([1,2,3],[4,5,6],[7,8,9])
-- Rose (1,4) [Rose (2,5) [],Rose (3,6) []]
-- (Rose 1 [Rose 2 [],Rose 3 []],Rose 4 [Rose 5 [],Rose 6 []])
main = do
  let ps = gzip ([1..3], [4..6], [7..9]) :: [(Int, Int, Int)]
  let ns = gzip (Rose 1 [Rose 2 [], Rose 3 []], Rose 4 [Rose 5 [], Rose 6 []]) :: Rose (Int, Int)
  print ps
  print $ gunzip ps
  print ns
  print $ gunzip ns
