import Data.Function
import Data.Char
import Data.Maybe
import Data.List
import Control.Applicative hiding (many)
import Control.Monad
import Control.Arrow
import Control.Monad.Trans.State

infixr 4 <:>
(<:>) :: Monad m => m a -> m [a] -> m [a]
(<:>) = liftM2 (:)

type Parser = StateT String Maybe
parser = StateT
parse  = runStateT

anyToken :: Parser Char
anyToken = parser $ \s -> case s of
	[]    -> Nothing
	(c:s) -> Just (c, s)

notFollowedBy :: Parser a -> Parser ()
notFollowedBy p = parser $ \s -> case parse p s of
	Nothing -> Just ((), s)
	_       -> Nothing

lookAhead :: Parser a -> Parser a
lookAhead p = parser $ \s -> second (const s) <$> parse p s

eof :: Parser ()
eof = notFollowedBy anyToken

satisfy :: (Char -> Bool) -> Parser Char
satisfy = flip mfilter anyToken

alpha = satisfy isAlpha
digit = satisfy isDigit
char  = satisfy . (==)
space = satisfy isSpace

choice :: [Parser a] -> Parser a
choice = msum

oneOf :: String -> Parser Char
oneOf = choice . map char

string :: String -> Parser String
string = foldr ((<:>) . char) (return "")

option :: a -> Parser a -> Parser a
option x p = p <|> return x

many :: Parser a -> Parser [a]
many p = option [] $ many1 p

many1 :: Parser a -> Parser [a]
many1 p = p <:> many p

defManyTill :: Parser [a] -> Parser a -> Parser b -> Parser [a]
defManyTill d p e =  (e *> return [])
                 <|> (p <:> defManyTill d p e)
                 <|>  d

manyTill :: Parser a -> Parser b -> Parser [a]
manyTill = defManyTill mzero

manyOrTill :: Parser a -> Parser b -> Parser [a]
manyOrTill = defManyTill (return [])

sep1By :: Parser a -> Parser b -> Parser [a]
sep1By p s = p <:> many (s *> p)

sepBy :: Parser a -> Parser b -> Parser [a]
sepBy p s = option [] $ sep1By p s

skip :: Parser a -> Parser ()
skip p = p *> return ()

------------------------------------------------------------------

lexeme p = many space *> p

lchar   = lexeme . char
lstring = lexeme . string

fully = skip space <|> eof

------------------------------------------------------------------

type Sym = String

data Term = Var Sym | Lam Sym Term | App Term Term deriving Show

keyword = choice $ map (\s -> lookAhead $ lstring s <* fully)
	["where", "end"]

ident = lexeme $  (char '_' <|> alpha)
              <:> (many $ alpha <|> digit <|> oneOf "_\'")

parseOne =   Var <$> ident
		<|> (lchar '(' *> parseTerm <* lchar ')')

parseAlone =  (flip $ foldr Lam)
          <$> (option [] $ lchar '\\' *> many1 ident <* lchar '.')
          <*> (foldl1 App <$> parseOne `manyOrTill` keyword <|> parseAlone)

parseAss =  (,)
		<$> ident
		<*> (flip (foldr Lam) <$> many ident <*> (lchar '=' *> parseTerm))

parseTerm =   foldr (\(s, e2) e1 -> App (Lam s e1) e2)
         <$>  parseAlone
         <*> (option [] $ lstring "where"
         		    *> parseAss `sepBy` lchar ';'
         		    <* lstring "end")
         			    
lparser = parseTerm <* eof

------------------------------------------------------------------

pretty = tail . pretty' where
    pretty' (Var s)     = " " ++ s
    pretty' (App e1 e2) = (case e1 of
        Lam _ _ -> " (" ++ pretty e1 ++ ") "
        _       -> " "  ++ pretty e1 ++ " "
        ) ++ case e2 of
        Var s2  -> s2
        _       -> "(" ++ pretty e2 ++ ")"
    pretty'  e          = " \\" ++ tail (pretty'' e) where
        pretty'' (Lam s e) = " " ++ s ++ pretty'' e
        pretty''  e        = ". " ++ pretty e

------------------------------------------------------------------

freeVars (Var s)     = [s]
freeVars (Lam s e)   = freeVars e  \\ [s]
freeVars (App e1 e2) = freeVars e1 `union` freeVars e2

subst s1 e2 = subst' where
    subst' e1@(Var s1')
        | s1 == s1' = e2
        | otherwise = e1
    subst' e1@(Lam s1' e1')
        | s1 == s1'                            = e1
        | s1' == "_" || s1' `notElem` frees_e2 = Lam s1' (subst' e1')
        | otherwise                            = Lam s1'' e1'' where
            frees_e2     = freeVars e2
            frees_e2_e1' = frees_e2 `union` freeVars e1'
            s1'' = until (`notElem` frees_e2_e1') ('\'':) s1'
            e1'' = subst' (subst s1' (Var s1'') e1')
    subst' (App e1'1 e1'2) = App (subst' e1'1) (subst' e1'2)

-- Beta-reduction

eager into   (App e1 e2) = case (eager into e1, eager into e2) of
	(Lam s1 e1, e2') -> eager into (subst s1 e2' e1)
	(e1'      , e2') -> App e1' e2'
eager into l@(Lam s e)   = if into then Lam s (eager into e) else l
eager _    v             = v

byvalue = eager False
full    = eager True

------------------------------------------------------------------

main = do
	s <- getContents
	putStrLn $ case parse parseTerm s of
		Just (t, _) -> pretty $ full $ byvalue t
		_           -> "Nothing"

-- Example input:
{-leq (s (s (s (s z)))) (s (s z)) where
	true  = \p _. p;
	false = \_ q. q;
	or    = \p q. p p q;
        z    = \_ z. z;
        s    = \n s z. s (n s z);
        eq0  = \n. n (\_. false) true;
        plus = \m n s z. m s (n s z);
        pred = \n s z. n (\g h. h (g s)) (\_. z) (\x. x);
        sub  = \n m. m pred n;
        leq  = \n m. eq0 (sub n m)
end-}
