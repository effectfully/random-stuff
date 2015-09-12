{-# LANGUAGE GADTs, DataKinds, TypeFamilies, TemplateHaskell #-}

import Data.Functor
import Data.Singletons.TH
import Data.Singletons.Prelude

$(singletons [d| data Nat = Z | S Nat |])

data HomoFree n f a where
    Pure :: a -> HomoFree Z f a
    Free :: f (HomoFree n f a) -> HomoFree (S n) f a

mapFree :: Functor f => (a -> b) -> HomoFree n f a -> HomoFree n f b
mapFree f (Pure  x) = Pure (f x)
mapFree f (Free fx) = Free (mapFree f <$> fx)

type family IterN n f a where
  IterN  Z    f a = a
  IterN (S n) f a = f (IterN n f a)

runFree :: Functor f => HomoFree n f a -> IterN n f a
runFree (Pure  x) = x
runFree (Free fx) = runFree <$> fx

lowerFree :: (Functor f, SingI n) => HomoFree (S n) f a -> HomoFree n f (f a)
lowerFree = go sing where
    go :: Functor f => Sing n -> HomoFree (S n) f a -> HomoFree n f (f a)
    go  SZ    (Free fx) = Pure $ runFree <$> fx
    go (SS n) (Free fx) = Free $ go n <$> fx

xs = Free [Free [Pure 1, Pure 2], Free [Pure 3, Pure 4, Pure 5]]

main = do
    print $ runFree . mapFree (+ 1)           $ xs -- [[2,3],[4,5,6]]
    print $ runFree . mapFree sum . lowerFree $ xs -- [3,12]