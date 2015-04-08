-- related to http://stackoverflow.com/questions/29487773/how-to-build-a-typed-variadic-function-from-a-container

{-# LANGUAGE GADTs, KindSignatures, DataKinds, PolyKinds, TypeFamilies, TypeOperators, UndecidableInstances #-}

type family If b x y where
    If True  x y = x
    If False x y = y

data Booly :: Bool -> * where
    Truly :: Booly True
    Falsy :: Booly False

data Nat = Z | S Nat

data Natty :: Nat -> * where
    Zy :: Natty Z
    Sy :: Natty n -> Natty (S n)

data Listy (b :: a -> *) :: [a] -> * where
    Nilly :: Listy b '[]
    Consy :: b x -> Listy b xs -> Listy b (x ': xs)

type Natties = Listy Natty

type family NatEq n m :: Bool where
    NatEq  Z     Z    = True
    NatEq  Z    (S m) = False
    NatEq (S n)  Z    = False
    NatEq (S n) (S m) = NatEq n m

type family Adder (ns :: [Nat]) :: * where
    Adder '[]       = Int
    Adder (n ': ns) = If (NatEq n (S (S (S (S (S Z)))))) Int (Int -> Adder ns)

nattyEq :: Natty n -> Natty m -> Booly (NatEq n m)
nattyEq  Zy     Zy    = Truly
nattyEq  Zy    (Sy m) = Falsy
nattyEq (Sy n)  Zy    = Falsy
nattyEq (Sy n) (Sy m) = nattyEq n m

adder :: Natties ns -> Adder ns
adder = go 0 where
    go :: Int -> Natties ns -> Adder ns
    go i  Nilly       = 0
    go i (Consy n ns) = case nattyEq n (Sy (Sy (Sy (Sy (Sy Zy))))) of
        Truly -> i + 100
        Falsy -> \a -> go (i + a) ns

list = Consy Zy $ Consy (Sy Zy) $ Consy (Sy (Sy (Sy (Sy (Sy Zy))))) $ Consy Zy $ Nilly

main = do
    print $ adder (Consy Zy $ Consy (Sy Zy) $ Nilly) 3 9 -- 0
    print $ adder list 6 8                               -- 114
    print $ adder (Consy (Sy (Sy Zy)) list) 1 2 3        -- 106
