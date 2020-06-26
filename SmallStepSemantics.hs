module SmallStepSemantics where

import           SimplyTypedLambdaCalc
import           Data.Set
import           System.IO.Unsafe


pop :: Stack -> (Frame, Stack)
pop (x : xs) = (x, xs)
pop []       = error "It is not possible to pop an empty stack"

push :: Frame -> Stack -> Stack
push x xs = x : xs

done :: Stack -> Bool
done (h : _) | h == halt = True
             | otherwise = False
done _ = False

initialStack :: Stack
initialStack = [halt]

isValue :: Expr -> Bool
isValue Taut        = True
isValue (Var _    ) = True
isValue (Lam _ _ _) = True
isValue (Pair x y ) = isValue x && isValue y
isValue (Inl  x _ ) = isValue x
isValue (Inr  x _ ) = isValue x
isValue _           = False


{- SEMANTICS -}
smallStep :: (Expr, Stack) -> (Expr, Stack)
smallStep (e, k)
   | isValue e && done k = (e, k)
   | isValue e = case pop k of
      (App (Lam x a m) h, ks) | h == hole -> (subst x e m, ks)
      (App h n, ks) | h == hole           -> (n, push (App e hole) ks)
      (Pair h n, ks) | h == hole          -> (n, push (Pair e hole) ks)
      (Pair v h, ks) | h == hole          -> (Pair v e, ks)
      (Fst h, ks) | h == hole             -> case e of
         Pair v w  -> (v, ks)
         otherwise ->
            error ("The value " ++ show e ++ " is not a product-value")
      (Snd h, ks) | h == hole -> case e of
         Pair v w  -> (w, ks)
         otherwise ->
            error ("The value " ++ show e ++ " is not a product-value")
      (Inl h a, ks) | h == hole             -> (Inl e a, ks)
      (Inr h a, ks) | h == hole             -> (Inr e a, ks)
      (VCase h x1 n1 x2 n2, ks) | h == hole -> case e of
         Inl v a   -> (subst x1 v n1, ks)
         Inr v a   -> (subst x2 v n2, ks)
         otherwise -> error
            ("The value " ++ show e ++ " is neither a inl- nor a inr-value")
      otherwise -> error
         (  "The value "
         ++ show e
         ++ " could not be matched with the expression "
         ++ show (fst (pop k))
         ++ " on top of the stack."
         )
   | otherwise = case e of
      Abort m a           -> (m, push (Abort hole a) k)
      App   m n           -> (m, push (App hole n) k)
      Pair  m n           -> (m, push (Pair hole n) k)
      Fst m               -> (m, push (Fst hole) k)
      Snd m               -> (m, push (Snd hole) k)
      Inl m a             -> (m, push (Inl hole a) k)
      Inr m a             -> (m, push (Inr hole a) k)
      VCase m x1 n1 x2 n2 -> (m, push (VCase hole x1 n1 x2 n2) k)
      LetCC x a m         -> (substStack x k m, k)
      Throw k e           -> (e, k)

bigStep :: Expr -> Expr
bigStep e = fst (iterate smallStep (e, initialStack))
   where iterate f x = let y = f x in if x == y then y else iterate f y

bigStepPrint :: Expr -> Expr
bigStepPrint e = fst (iterate smallStep (e, initialStack))
 where
  iterate f x = seq (unsafePerformIO (print x))
                    (let y = f x in if x == y then y else iterate f y)



{- EXAMPLES -}
-- Example from section 3.3.1 
exampleLetcc  = orLO false (LetCC "alpha" bool (orLO true (Throw (stackVar "alpha") false)))

-- Example from section 3.3.4
-- Here M = \y:a. true
exampleCallcc = andLO true (callcc "x" bool (TVar "psi") (App (Lam "y" (TVar "psi") true) (App (Var "x") false)))

-- Example from section 3.4
catch :: String -> Type -> Expr -> Expr
catch k a t = delta k a (Throw (stackVar k) t)

-- The first, inefficient version
andS :: [Expr] -> Expr
andS []       = true
andS (r : rs) | r == true || r == false = andLO r (andS rs)
              | otherwise  = error "geen bools"

-- The second, more efficient implementation using catch and Throw
andS2 :: [Expr] -> Expr
andS2 xs = catch "k" bool (andShelp xs (stackVar "k"))
     where andShelp [] k       = true
           andShelp (r : rs) k | bigStep r == true  = andShelp rs k
                               | bigStep r == false = Throw k false
                               | otherwise          = error "geen bools"


