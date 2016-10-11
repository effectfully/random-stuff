{-# LANGUAGE ScopedTypeVariables, KindSignatures, GADTs, DataKinds, PolyKinds, TypeFamilies, TemplateHaskell, BangPatterns #-}

import Data.Monoid
import Data.Array
import Data.Singletons
import Data.Singletons.TH

$(singletons [d|
  data Nat = Z | S Nat
  |])

toInt :: Nat -> Int
toInt = go 0 where
  go !a  Z    = a
  go  a (S n) = go (1 + a) n

newtype Vec (n :: Nat) a = Vec [a]
                         deriving (Eq, Ord, Show)

instance Ix a => Ix (Vec n a) where
  range   (Vec ns, Vec ms)          = map Vec . sequence $ zipWith (curry range) ns ms
  index   (Vec ns, Vec ms) (Vec ps) = foldr (\(i, r) a -> i + r * a) 0 $
    zipWith3 (\n m p -> (index (n, m) p, rangeSize (n, m))) ns ms ps
  inRange (Vec ns, Vec ms) (Vec ps) = and $ zipWith3 (curry inRange) ns ms ps

newtype Sized m (ns :: [Nat]) a = Sized { getArray :: Array (Vec m Int) a }

vecBounds :: forall m (ns :: [Nat]). SingI m => Sing ns -> (Vec m Int, Vec m Int)
vecBounds singNs = (Vec $ replicate m 0, Vec ns') where
    m   = toInt $ fromSing (sing :: Sing m)
    ns' = map (pred . toInt) $ fromSing singNs

listSized :: forall m (ns :: [Nat]) a. (SingI m, SingI ns) => [a] -> Sized m ns a
listSized = Sized . listArray (vecBounds (sing :: Sing ns))

instance (SingI m, SingI ns, Monoid a) => Monoid (Sized m ns a) where
  mempty                      = listSized $ repeat mempty
  Sized as `mappend` Sized bs = listSized $ zipWith mappend (elems as) (elems bs)

type M  = S (S (S Z))
type Ns = [S (S Z), S Z, S (S (S Z))]

arr1 :: Sized M Ns (Sum Int)
arr1 = listSized $ map Sum [5,3,6,7,1,4]

arr2 :: Sized M Ns (Sum Int)
arr2 = listSized $ map Sum [8,2,9,7,3,6]

main = mapM_ (print . getArray) $ [arr1, arr2, arr1 `mappend` arr2 `mappend` mempty]
