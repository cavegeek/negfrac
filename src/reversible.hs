{-

This is an EDSL in Haskell implementing the language described in Section 2 of
James and Sabry's paper
"The Two Dualities of Computation: Negative and Fractional Types".
The language described in later sections is implemented in another file.

This implementation is not by them. I am doing it to better understand the
paper. I hope it helps others too.

-}

{-# LANGUAGE GADTs #-}

{-
We'll use GADTs to make Haskell's type system to the type checking for us.
We'll use Haskell's types, so to map from the paper:
  0 ==> Void
  1 ==> ()
  a + b ==> Either a b
  a X b ==> (a,b)
-}

data Void

data Comb a where
  Zeroe :: Comb (Either Void a -> a)
  Zeroi :: Comb (a -> Either Void a)
  Swapa :: Comb (Either a b -> Either b a)
  Assocla :: Comb (Either a (Either b c) -> Either (Either a b) c)
  Assocra :: Comb (Either (Either a b) c -> Either a (Either b c))
  Unite :: Comb (((),b) -> b)
  Uniti :: Comb (b -> ((),b))
  Swapm :: Comb ((a,b) -> (b,a))
  Assoclm :: Comb ((a,(b,c)) -> ((a,b),c))
  Assocrm :: Comb (((a,b),c) -> (a,(b,c)))
  Distrib0 :: Comb ((Void,b) -> Void)
  Factor0 :: Comb (Void -> (Void,b))
  Distrib :: Comb (((Either a b),c) -> Either (a,c) (b,c))
  Factor :: Comb (Either (a,c) (b,c) -> ((Either a b), c))

  Id :: Comb (a -> a)
  (:.:) :: Comb (a -> b) -> Comb (b -> c) -> Comb (a -> c)
  (:+:) :: Comb (a -> b) -> Comb (c -> d) -> Comb (Either a c -> Either b d)
  (:*:) :: Comb (a -> b) -> Comb (c -> d) -> Comb ((a,c) -> (b,d))

  Sym :: Comb (a -> b) -> Comb (b -> a)

evaluate :: Comb (a -> b) -> a -> b
evaluate Zeroe (Right x) = x
evaluate Zeroi x = Right x
evaluate Swapa (Left x) = Right x
evaluate Swapa (Right x) = Left x
evaluate Assocla (Left x) = Left (Left x)
evaluate Assocla (Right (Left x)) = Left (Right x)
evaluate Assocla (Right (Right x)) = Right x
evaluate Assocra (Left (Left x)) = Left x
evaluate Assocra (Left (Right x)) = Right (Left x)
evaluate Assocra (Right x) = Right (Right x)
evaluate Unite ((),x) = x
evaluate Uniti x = ((),x)
evaluate Swapm (x,y) = (y,x)
evaluate Assoclm (x,(y,z)) = ((x,y),z)
evaluate Assocrm ((x,y),z) = (x,(y,z))
evaluate Distrib (Left x,y) = Left (x,y)
evaluate Distrib (Right x,y) = Right (x,y)
evaluate Factor (Left (x,y)) = (Left x,y)
evaluate Factor (Right (x,y)) = (Right x,y)

evaluate Id x = x
evaluate (c :.: d) x = evaluate d (evaluate c x)
evaluate (c :+: d) (Left x) = Left (evaluate c x)
evaluate (c :+: d) (Right x) = Right (evaluate d x)
evaluate (c :*: d) (x,y) = (evaluate c x, evaluate d y)

evaluate (Sym Zeroe) x = evaluate Zeroi x
evaluate (Sym Zeroi) x = evaluate Zeroe x
evaluate (Sym Swapa) x = evaluate Swapa x
evaluate (Sym Assocla) x = evaluate Assocra x
evaluate (Sym Assocra) x = evaluate Assocla x
evaluate (Sym Unite) x = evaluate Uniti x
evaluate (Sym Uniti) x = evaluate Unite x
evaluate (Sym Swapm) x = evaluate Swapm x
evaluate (Sym Assoclm) x = evaluate Assocrm x
evaluate (Sym Assocrm) x = evaluate Assoclm x
evaluate (Sym Distrib0) x = evaluate (Factor0) x
evaluate (Sym Factor0) x = evaluate Distrib0 x
evaluate (Sym Distrib) x = evaluate Factor x
evaluate (Sym Factor) x = evaluate Distrib x
evaluate (Sym Id) x = evaluate Id x
evaluate (Sym (Sym c)) x = evaluate c x
evaluate (Sym (c :.: d)) x = evaluate (Sym d :.: Sym c) x
evaluate (Sym (c :+: d)) x = evaluate (Sym c :+: Sym d) x
evaluate (Sym (c :*: d)) x = evaluate (Sym c :*: Sym d) x

{-
Example
-}

type EBool = Either () ()

efalse = Left ()
etrue = Right ()

-- Negate the right bool only when the left is true.
example0 :: Comb ((EBool,EBool) -> (EBool, EBool))
example0 = Distrib :.: (Id :+: (Id :*: Swapa)) :.: Factor

main = do
  x <- readLn
  putStrLn (show (evaluate example0 x))
