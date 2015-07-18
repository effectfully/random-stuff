import Data.Either
import Data.List
import Data.Maybe
import Data.Functor

subst :: Char -> String -> Either Char String -> Either Char String
subst p xs (Left q) | p == q = Right xs
subst p xs       q           = q

matches :: String -> String -> Bool
matches = go . map Left where
  go            []  [] = True
  go (Left  p : ps) xs = or [ go (map (subst p ixs) ps) txs
                            | (ixs, txs) <- tail $ zip (inits xs) (tails xs) ]
  go (Right s : ps) xs = fromMaybe False $ go ps <$> stripPrefix s xs
  go            _   _  = False

main = mapM_ (print . uncurry matches)
        [ ("abba"    , "redbluebluered"                    ) -- True
        , ("abba"    , "redblueblue"                       ) -- False
        , ("abb"     , "redblueblue"                       ) -- True
        , ("aab"     , "redblueblue"                       ) -- False
        , ("cbccadbd", "greenredgreengreenwhiteblueredblue") -- True
        ]
