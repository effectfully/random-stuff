-- A lightweight and not very expressive alternative to monad transformers.

{-# LANGUAGE TypeOperators, ConstraintKinds #-}

import Data.Foldable    as F
import Data.Traversable as T
import Control.Monad
import Control.Applicative
import Text.Read hiding (lift)

type NestedMonads m t = (Monad m, Traversable t, Monad t)

rereturn :: (Monad m, Monad n) => a -> m (n a)
rereturn = return . return

liliftM :: (Monad m, Monad n) => (a -> b) -> m (n a) -> m (n b)
liliftM = liftM . liftM

jojoin :: NestedMonads m t => m (t (m (t a))) -> m (t a)
jojoin = (>>= liftM join . T.sequence)

bibind :: NestedMonads m t => m (t a) -> (a -> m (t b)) -> m (t b)
bibind x f = jojoin (liliftM f x)

newtype (f :. g) a = Nested { getNested :: f (g a) }

instance (Monad m, Traversable t, Monad t) => Monad (m :. t) where
	return  = Nested . rereturn
	x >>= f = Nested $ getNested x `bibind` (getNested . f)

type Nested = (:.)

tfil :: NestedMonads m t => t a -> Nested m t a
tfil = Nested . return

lift :: NestedMonads m t => m a -> Nested m t a
lift = Nested . liftM return

main :: IO (Maybe ())
main = getNested $ do
	x <- Nested $ readMaybe <$> getLine :: Nested IO Maybe Int
	lift $ print x
