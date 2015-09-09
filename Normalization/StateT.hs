import Control.Monad
import Control.Monad.Trans.State

infixr 2 :->
infixl 4 :$

data Type    = I | Type :-> Type
data Term    = Var Int | Lam Term | Term :$ Term deriving Show
type STerm m = StateT Int m Term
data Sem m   = STerm (STerm m) | Fun (Sem m -> Sem m)
type Con m   = [Sem m]

app :: Sem m -> Sem m -> Sem m
app (Fun f) x = f x

eval :: Con m -> Term -> Sem m
eval rho (Var i)  = rho !! i
eval rho (Lam b)  = Fun (\x -> eval (x : rho) b)
eval rho (f :$ x) = app (eval rho f) (eval rho x)

reflect :: Monad m => Type -> STerm m -> Sem m
reflect  I        t = STerm t
reflect (s :-> t) f = Fun (\x -> reflect t (liftM2 (:$) f (reify s x)))

reify :: Monad m => Type -> Sem m -> STerm m
reify  I        (STerm t) = t
reify (s :-> t) (Fun   f) = do
    i <- get
    put (succ i)
    liftM Lam (reify t (f (reflect s (liftM (\j -> Var (j - i - 1)) get))))

norm :: Monad m => Type -> Term -> m Term
norm s t = evalStateT (reify s (eval [] t)) 0