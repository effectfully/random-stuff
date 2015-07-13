import Data.Maybe
import Data.List
import Control.Applicative
import Control.Monad
import Control.Arrow
import Control.Monad.Trans.State

lookupDelete k [] =  Nothing
lookupDelete k ((x, y):xys)
    | k == x    = Just (y, xys)
    | otherwise = second ((x, y):) <$> lookupDelete k xys

finish (x, []) = Just x
finish  _      = Nothing

type Parser a = StateT [(String, String)] Maybe a

option :: (String -> Maybe a) -> String -> Parser a
option f str = StateT $ \xs -> do
	(v, xs') <- lookupDelete str xs
	v' <- f v
	return (v', xs')

string :: String -> Parser String
string = option Just

value :: Read a => String -> Parser a
value = option $ reads >>> listToMaybe >=> finish

optPairs  []                  = Just []
optPairs (('-':'-':x1):x2:xs) = ((x1, x2) :) <$> optPairs xs
optPairs  _                   = Nothing

parse :: Parser a -> String -> Maybe a
parse p = words >>> optPairs >=> runStateT p >=> finish

-- An example.

data User = User
	{ userName :: String
	, userId :: Integer
	, userDbls :: (Double, Double)
	} deriving Show

userParser :: Parser User
userParser = User <$> string "name" <*> value "id" <*> value "dbls"
	
main = interact $ unlines . map (show . parse userParser) . lines
