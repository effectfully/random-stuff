data Type  = Iota | Arrow Type Type
data Term  = Var Int | Lam Term | App Term Term
type ITerm = Int -> Term
data Plain = Val ITerm | Fun (Plain -> Plain)

reflect :: Type -> ITerm -> Plain
reflect  Iota       tv = Val tv
reflect (Arrow s t) tf = Fun (\x -> reflect t (\i -> App (tf i) (reify s x i)))

reify :: Type -> Plain -> ITerm
reify  Iota       (Val v) = v
reify (Arrow s t) (Fun f) = \i -> Lam (reify t (f (reflect s (\j -> Var (j - i - 1)))) (i + 1))

type Con = [Plain]

app (Fun f) = f

plain :: Con -> Term -> Plain
plain rho (Var i)   = rho !! i
plain rho (Lam b)   = Fun (\x -> plain (x : rho) b)
plain rho (App f x) = app (plain rho f) (plain rho x)

normalize :: Type -> Term -> Term
normalize t e = reify t (plain [] e) 0