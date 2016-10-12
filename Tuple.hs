{-# LANGUAGE KindSignatures, ScopedTypeVariables, RankNTypes, MultiParamTypeClasses, TypeFamilies #-}

import Data.Proxy
import Data.Constraint hiding ((&&&), (***))
import Data.Biapplicative
import Control.Applicative
import Control.Arrow

class Splittable f g where
  split :: f a -> g a (f a)
  
class Tuple t where
  type Map (f :: * -> *) t

  nilMap   :: Proxy t -> (forall a. f a) -> Map f t
  consMap  :: (forall a. a -> f a -> f a) -> t -> Map f t -> Map f t
  splitMap :: (Biapplicative g, Splittable f g) => Proxy (f t) -> Map f t -> g t (Map f t)

instance Tuple (a, b) where
  type Map f (a, b) = (f a, f b)

  nilMap _ a = (a, a)
  consMap f (x, y) (a, b) = (f x a, f y b)
  splitMap _ (a, b) = biliftA2 (,) (,) (split a) (split b)

instance Tuple (a, b, c) where
  type Map f (a, b, c) = (f a, f b, f c)

  nilMap _ a = (a, a, a)
  consMap f (x, y, z) (a, b, c) = (f x a, f y b, f z c)
  splitMap _ (a, b, c) = biliftA3 (,,) (,,) (split a) (split b) (split c)

gunzip :: forall t. Tuple t => [t] -> Map [] t
gunzip = foldr (consMap (:)) $ nilMap (Proxy :: Proxy t) []

newtype MaybeBoth a b = MaybeBoth { getMaybeBoth :: Maybe (a, b) }

instance Bifunctor MaybeBoth where
  bimap f g (MaybeBoth a) = MaybeBoth $ (f *** g) <$> a

instance Biapplicative MaybeBoth where
  bipure x y = MaybeBoth $ Just (x, y)
  MaybeBoth f <<*>> MaybeBoth a = MaybeBoth $ uncurry (***) <$> f <*> a
  
instance Splittable [] MaybeBoth where
  split  []    = MaybeBoth Nothing
  split (x:xs) = bipure x xs

gzip :: forall t. Tuple t => Map [] t -> [t]
gzip a = maybe [] (\(p, a') -> p : gzip a') . getMaybeBoth $ splitMap (Proxy :: Proxy [t]) a

-- [(1,4,7),(2,5,8),(3,6,9)]
-- ([1,2,3],[4,5,6],[7,8,9])
main = do
  let ps = gzip ([1..3], [4..6], [7..9]) :: [(Int, Int, Int)]
  print ps
  print $ gunzip ps
