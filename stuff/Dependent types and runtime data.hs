-- This is related to http://stackoverflow.com/questions/27029564/how-do-i-build-a-list-with-a-dependently-typed-length/

{-# LANGUAGE GADTs, KindSignatures, DataKinds, PolyKinds, RankNTypes, TypeOperators #-}

import Data.Either
import Data.Functor
import Control.Monad

data Nat = Z | S Nat

data Natty :: Nat -> * where
	Zy :: Natty Z
	Sy :: Natty n -> Natty (S n)

data Finny :: Nat -> Nat -> * where
	FZ :: Finny (S n) Z
	FS :: Finny n m -> Finny (S n) (S m)

type Finny0 n = Finny (S n)

data Vec :: * -> Nat -> * where
  VNil :: Vec a Z
  VCons :: a -> Vec a n -> Vec a (S n) 

fromIntNatty :: Int -> (forall n. Natty n -> b) -> b
fromIntNatty 0 f = f Zy
fromIntNatty n f = fromIntNatty (n - 1) (f . Sy)

fromNattyFinny0 :: Natty n -> (forall m. Finny0 n m -> b) -> b
fromNattyFinny0  Zy    f = f FZ
fromNattyFinny0 (Sy n) f = fromNattyFinny0 n (f . FS)

fromIntNattyFinny0 :: Int -> (forall n m. Natty n -> Finny0 n m -> b) -> b
fromIntNattyFinny0 n f = fromIntNatty n $ \n'' -> fromNattyFinny0 n'' (f n'')

vfromList :: [a] -> (forall n. Vec a n -> b) -> b
vfromList    []  f = f VNil
vfromList (x:xs) f = vfromList xs (f . VCons x)

vhead :: Vec a (S n) -> a
vhead (VCons x xs) = x

vtoList :: Vec a n -> [a]
vtoList  VNil        = []
vtoList (VCons x xs) = x : vtoList xs

vlength :: Vec a n -> Natty n
vlength  VNil        = Zy
vlength (VCons x xs) = Sy (vlength xs)

vlookup :: Finny n m -> Vec a n -> a
vlookup  FZ    (VCons x xs) = x
vlookup (FS i) (VCons x xs) = vlookup i xs

vtake :: Finny0 n m -> Vec a n -> Vec a m
vtake  FZ     _           = VNil
vtake (FS i) (VCons x xs) = VCons x (vtake i xs)
			
data (:<=) :: Nat -> Nat -> * where
	Z_le_Z :: Z :<= m
	S_le_S :: n :<= m -> S n :<= S m

type n :< m = S n :<= m

(<=?) :: Natty n -> Natty m -> Either (m :< n) (n :<= m)
Zy   <=? m    = Right Z_le_Z
Sy n <=? Zy   = Left (S_le_S Z_le_Z)
Sy n <=? Sy m = either (Left . S_le_S) (Right . S_le_S) $ n <=? m

inject0Le :: Finny0 n p -> n :<= m -> Finny0 m p
inject0Le  FZ     _          = FZ
inject0Le (FS i) (S_le_S le) = FS (inject0Le i le)

main = do
	xs <- readLn :: IO [Int]
	ns <- readLn
	forM_ ns $ \n -> putStrLn $
		fromIntNattyFinny0 n $ \n' i' ->
		vfromList xs         $ \xs'   ->
		case n' <=? vlength xs' of
			Left  _  -> "What should I do with this input?"
			Right le -> show $ vtoList $ vtake (inject0Le i' le) xs'