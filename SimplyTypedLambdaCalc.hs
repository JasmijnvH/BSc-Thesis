module SimplyTypedLambdaCalc where

import           MultiMap                      as MM
import           Data.Set                      as S
import           Control.Monad.State

data Type = TVar    String
          | Unit
          | Error
          | Func    Type Type
          | Product Type Type
          | Sum     Type Type
          deriving (Eq)

data Expr = Var   String
          | Taut                                  -- Unit I
          | Abort Expr Type                       -- Error E
          | Lam   String Type Expr                -- ->I
          | App   Expr Expr                       -- ->E
          | Pair  Expr Expr                       -- /\I
          | Fst   Expr                            -- /\E
          | Snd   Expr                            -- /\E
          | Inl   Expr Type                       -- \/I
          | Inr   Expr Type                       -- \/I
          | VCase Expr String Expr String Expr    -- \/E
          | LetCC String Type Expr                -- Peirce
          | Throw Stack Expr                      -- Derive contradiction
          deriving (Eq)


type Stack = [Frame] 

type Frame = Expr
{- Frames are expressions containing precisely one occurrence of the special variable _ (which we call a "hole") -}

stackToExpr :: Stack -> Type -> Expr
stackToExpr st a = Lam holeSym a (body st)
   where
      body []       = Var holeSym
      body (x : xs) = subst holeSym x (body xs)

hole :: Frame
hole = Var holeSym

holeSym :: String
holeSym = "_"

frameVar :: String -> Frame
frameVar x = App (Var x) hole

stackVar :: String -> Stack
stackVar x = [frameVar x]

halt :: Frame
halt = frameVar "halt"


instance Show Type where
      show (TVar a) = a
      show Unit     = "1"
      show Error    = "0"
      show (Func a b) | b == Error = "-" ++ show a
                      | otherwise  = "(" ++ show a ++ " -> " ++ show b ++ ")"
      show (Product a b) = "(" ++ show a ++ " /\\ " ++ show b ++ ")"
      show (Sum a b)
            | a == Unit && b == Unit = "Bool"
            | otherwise              = "(" ++ show a ++ " \\/ " ++ show b ++ ")"

instance Show Expr where
      show (Var x)     = x
      show Taut        = "<>"
      show (Abort t a) = "abort:" ++ show a ++ " {" ++ show t ++ "}"
      show (Lam x a t) =
            "(lambda " ++ x ++ ":" ++ show a ++ " . " ++ show t ++ ")"
      show (App t1 t2) = case t1 of
            Lam x a n ->
                  "(let " ++ x ++ " = " ++ show t2 ++ " in " ++ show n ++ ")"
            otherwise -> "(" ++ show t1 ++ " " ++ show t2 ++ ")"
      show (Pair t1 t2) = "< " ++ show t1 ++ ", " ++ show t2 ++ " >"
      show (Fst t     ) = "p1(" ++ show t ++ ")"
      show (Snd t     ) = "p2(" ++ show t ++ ")"
      show (Inl t a) | t == Taut && a == bool = "false"
                     | otherwise = "inl^" ++ show a ++ "(" ++ show t ++ ")"
      show (Inr t a)
            | t == Taut && a == bool = "true"
            | otherwise              = "inr^" ++ show a ++ "(" ++ show t ++ ")"
      show (VCase t x1 s1 x2 s2) | notMember x1 (freeVariables s1) && notMember x2 (freeVariables s2) = "if (" ++ show t ++ ") then (" ++ show s2 ++ ") else (" ++ show s1 ++ ")"
             | otherwise = 
            "case ("
                  ++ show t
                  ++ ") of { "
                  ++ x1
                  ++ " -> "
                  ++ show s1
                  ++ " | "
                  ++ x2
                  ++ " -> "
                  ++ show s2
                  ++ " }"
      show (LetCC k a e) = "letcc " ++ k ++ " . " ++ show e
      show (Throw k e  ) = "throw " ++ show e ++ " to " ++ show k


{- SYNTACTIC SUGAR -}
notT :: Type -> Type
notT a = Func a Error

bool :: Type
bool = Sum Unit Unit

true :: Expr
true = Inr Taut bool

false :: Expr
false = Inl Taut bool

letIn :: String -> Type -> Expr -> Expr -> Expr
letIn x a m n = App (Lam x a n) m

ifthenelse :: Expr -> Expr -> Expr -> Expr
ifthenelse m t e = VCase m x1 e x2 t
   where
      x1 = newVariable "x" (freeVariables e) "\'"
      x2 = newVariable "y" (freeVariables t) "\'"


{- LOGICAL OPERATORS -}
-- Using these, the evaluation of programs with continuations is performed correctly
notLO :: Expr -> Expr
notLO p = ifthenelse p false true

andLO :: Expr -> Expr -> Expr
andLO p q = ifthenelse p (ifthenelse q true false) (ifthenelse q false false)

orLO :: Expr -> Expr -> Expr
orLO p q = ifthenelse p (ifthenelse q true true) (ifthenelse q true false)

xorLO :: Expr -> Expr -> Expr
xorLO p q = ifthenelse p (ifthenelse q false true) (ifthenelse q true false)

{- LAZY LOGICAL OPERATORS -}
andLOl :: Expr -> Expr -> Expr
andLOl p q = ifthenelse p (ifthenelse q true false) false

orLOl :: Expr -> Expr -> Expr
orLOl p q = ifthenelse p true (ifthenelse q true false)


{- CONTROL OPERATORS -}
-- Generalized Peirce's law : ((a -> b) -> a) -> a
-- x :: a -> b | m :: a     =>  callcc x a b m :: a 
callcc :: String -> Type -> Type -> Expr -> Expr
callcc k a b m = LetCC
      k'
      a
      (subst k (Lam y a (Abort (Throw (stackVar k') (Var y)) b)) m)
   where
      k' = newVariable k (freeVariables m) "\'"
      y  = newVariable "y" (S.insert k' (freeVariables m)) "\'"

-- Double negation elimination : --a -> a
-- k :: a -> Error | m :: Error     =>  delta k a m :: a
delta :: String -> Type -> Expr -> Expr
delta k a m = LetCC k a (Abort m a)

-- Law of excluded middle : a \/ -a
lem :: Type -> Expr
lem a = LetCC
      "k"
      (Sum a (notT a))
      (Inr
            (Lam "x" a (Throw (stackVar "k") (Inl (Var "x") (Sum a (notT a)))))
            (Sum a (notT a))
      )

-- Generalized law of excluded middle : a \/ (a -> b)
lemPlus :: Type -> Type -> Expr
lemPlus a b = callcc
      "k"
      (Sum a (Func a b))
      b
      (Inr
            (Lam "x" a (Throw (stackVar "k") (Inl (Var "x") (Sum a (Func a b))))
            )
            (Sum a (Func a b))
      )

-- DeMorgan's classical law : -(a /\ b) -> (-a \/ -b)
-- m :: -(a /\ b)      => deMorgan k a b m :: -a \/ -b
-- Not discussed in thesis
deMorgan :: Type -> Type -> Stack -> Expr
deMorgan a b m = LetCC
      "k"
      (Sum (notT a) (notT b))
      (Abort
            (Throw
                  m
                  (Pair
                        (LetCC
                              "k'"
                              a
                              (Abort
                                    (Throw
                                          (stackVar "k")
                                          (Inl (Var "k'")
                                               (Sum (notT a) (notT b))
                                          )
                                    )
                                    a
                              )
                        ) 
                        (LetCC
                              "k''"
                              b
                              (Abort
                                    (Throw
                                          (stackVar "k")
                                          (Inr (Var "k''")
                                               (Sum (notT a) (notT b))
                                          )
                                    )
                                    b
                              )
                        )
                  )
            )
            (Sum (notT a) (notT b))
      ) 

-- Alternative representation of deMorgan's law
deMorgan' :: Type -> Type -> Stack -> Expr
deMorgan' a b m = let k = newVariable "k" (freeStackVariables m) "" in
	  LetCC
      k
      (Sum (notT a) (notT b))
      (Inl
            (Lam
                  "x"
                  a
                  (Throw
                        (stackVar k)
                        (Inr
                              (Lam "y" b (Throw m (Pair (Var "x") (Var "y"))))
                              (Sum (notT a) (notT b))
                        )
                  )
            )
            (Sum (notT a) (notT b))
      )

-- Generalized DeMorgan's law : ((a /\ b) -> r) -> (a -> r \/ b -> r)
deMorganPlus :: Type -> Type -> Type -> Stack -> Expr
deMorganPlus a b r m = let k = newVariable "k" (freeStackVariables m) "" in
	  callcc
      k
      (Func a r)
      (Func b r)
      (Inl
            (Lam
                  "x"
                  a
                  (Throw
                        (stackVar k)
                        (Inr
                              (Lam "y" b (Throw m (Pair (Var "x") (Var "y"))))
                              (Sum (notT a) (notT b))
                        )
                  )
            )
            (Sum (notT a) (notT b))
      )

throw :: Stack -> Expr -> Type -> Expr
throw k v a = Abort (Throw k v) a

{- TYPE CHECKING -}
checkType :: Expr -> Type -> Bool
checkType e t = (inferType e) == t


{- TYPE INFERENCE -}
inferType :: Expr -> Type
inferType e = fst $ runState (inferTypeS e) MM.empty

inferTypeS :: Expr -> State (MM.MultiMap String Type) Type
inferTypeS (Var x) = do
      currentContext <- get
      case MM.lookup x currentContext of                 -- see if x is a bounded variable in the current scope
            Just v  -> return v                          -- if so, use its type
            Nothing -> error ("Undefined variable " ++ show (Var x))
inferTypeS (Taut     ) = return Unit
inferTypeS (Abort t a) = do
      at <- inferTypeS t
      case at of
            Error     -> return a
            otherwise -> error
                  (  "\'abort\' not possible of expression "
                  ++ show t
                  ++ " which has the non-error type "
                  ++ show at
                  )
inferTypeS (Lam x a t) = do
      currentContext <- get
      put (MM.insert x a currentContext)              -- add the lambda variable to the current environment
      b <- inferTypeS t                               -- infer the type of t using the adapted environment
      put currentContext                              -- remove the variable from the environment (out of scope)
      return (Func a b)
inferTypeS (App t1 t2) = do
      a <- inferTypeS t1
      b <- inferTypeS t2
      return (apply a b)
inferTypeS (Pair t1 t2) = do
      a <- inferTypeS t1
      b <- inferTypeS t2
      return (Product a b)
inferTypeS (Fst t) = do
      a <- inferTypeS t
      case a of
            Product x y -> return x
            otherwise   -> error
                  (  "\'fst\' not possible of expression "
                  ++ show t
                  ++ " which has the non-product type "
                  ++ show a
                  )
inferTypeS (Snd t) = do
      a <- inferTypeS t
      case a of
            Product x y -> return y
            otherwise   -> error
                  (  "\'snd\' not possible of expression "
                  ++ show t
                  ++ " which has the non-product type "
                  ++ show a
                  )
inferTypeS (Inl t a) = case a of
      Sum x y -> do
            b <- inferTypeS t
            if x == b
                  then return a
                  else error
                        (  "The type of the expression "
                        ++ show t
                        ++ " is "
                        ++ show b
                        ++ ". This does not correspond to the type "
                        ++ show x
                        ++ " of the left disjunct of the intended type "
                        ++ show a
                        )
      otherwise -> error
            ("\'inl\' not possible since the intended type is the non-sum type "
            ++ show a
            )
inferTypeS (Inr t a) = case a of
      Sum x y -> do
            b <- inferTypeS t
            if y == b
                  then return a
                  else error
                        (  "The type of the expression "
                        ++ show t
                        ++ " is "
                        ++ show b
                        ++ ". This does not correspond to the type "
                        ++ show y
                        ++ " of the right disjunct of the intended type "
                        ++ show a
                        )
      otherwise -> error
            ("\'inr\' not possible since the intended type is the non-sum type "
            ++ show a
            )
inferTypeS (VCase t x1 s1 x2 s2) = do
      at             <- inferTypeS t
      currentContext <- get
      put (MM.insert x1 (getLeft at) currentContext)
      as1 <- inferTypeS s1
      put currentContext
      put (MM.insert x2 (getRight at) currentContext)
      as2 <- inferTypeS s2
      put currentContext
      if as1 == as2
            then return as1
            else error
                  ("The two expressions used in the VCase are not of the same type. One is of type "
                  ++ show as1
                  ++ " while the other is of type "
                  ++ show as2
                  )
inferTypeS (LetCC k a t) = do
      currentContext <- get
      put (MM.insert k (Func a Error) currentContext)
      at <- inferTypeS t
      put currentContext
      if at == a
            then return at
            else error
                  (  "The type of the continuation, "
                  ++ show (Func a Error)
                  ++ " does not match the type of the expression, "
                  ++ show at
                  )
inferTypeS (Throw k e) = do
      b <- inferTypeS e
      a <- inferTypeS (stackToExpr k b)
      return (apply a b)

apply :: Type -> Type -> Type
apply (Func a b) c
      | a == c = b
      | otherwise = error
            (  "Invalid function application. The type "
            ++ show c
            ++ " does not correspond to the type "
            ++ show a
            )
apply a _ = error
      (  "Invalid function application. The type "
      ++ show a
      ++ " is not a function-type."
      )

getLeft :: Type -> Type
getLeft (Sum a b) = a
getLeft a =
      error ("Invalid case type. The type " ++ show a ++ " is not a sum-type.")

getRight :: Type -> Type
getRight (Sum a b) = b
getRight a =
      error ("Invalid case type. The type " ++ show a ++ " is not a sum-type.")


{- SUBSTITUTION -}
-- Capture avoiding substitution
subst :: String -> Expr -> Expr -> Expr
subst x e (Var y) | x == y    = e
                  | otherwise = Var y
subst _ _ Taut         = Taut
subst x e (Abort e' a) = Abort (subst x e e') a
subst x e (Lam y a e')
      | x == y = Lam y a e'
      |                                                                  -- The variable is bound, so we cannot perform the substitution
        otherwise = if notMember y (freeVariables e)
            then Lam y a (subst x e e')                                  -- y is not a free variable of e, so we can perform the substitution
            else subst x e alphaEq                                       -- y is a free variable of e, so we will perform the substitution on an alpha-equivalent expression
   where
      alphaEq       = alphaConvertLam (Lam y a e') usedVariables "\'"
      usedVariables = union (freeVariables e) (freeVariables e')         -- The free variables from e and e' cannot be used in determining the alpha-equivalent expression
subst x e (App  e' e'') = App (subst x e e') (subst x e e'')
subst x e (Pair e' e'') = Pair (subst x e e') (subst x e e'')
subst x e (Fst e'     ) = Fst (subst x e e')
subst x e (Snd e'     ) = Snd (subst x e e')
subst x e (Inl e' a   ) = Inl (subst x e e') a
subst x e (Inr e' a   ) = Inr (subst x e e') a
subst x e vc@(VCase e' y e'' z e''') =
      case (notMember y (freeVariables e), notMember z (freeVariables e)) of
            (True, True) ->
                  VCase (subst x e e') y (subst x e e'') z (subst x e e''')           -- Neither y nor z are free variables of e
            (True , False) -> subst x e alphaEqRight                                  -- y is not a free variable of e, but z is
            (False, True ) -> subst x e alphaEqLeft                                   -- y is a free variable of e, but z isn't      
            (False, False) -> subst x e alphaEqBoth                                   -- y and z both are free variables of e 
   where
      alphaEqRight  = alphaConvertVCaseRight vc usedVarsRight "\'"
      usedVarsRight = union (freeVariables e) (freeVariables e''')
      alphaEqLeft   = alphaConvertVCaseLeft vc usedVarsLeft "\'"
      usedVarsLeft  = union (freeVariables e) (freeVariables e'')
      alphaEqBoth   = alphaConvertVCaseRight alphaEqLeft usedVarsRight "\'"
subst x e (LetCC k a e')
      | x == k = LetCC k a e'
      | otherwise = if notMember k (freeVariables e)
            then LetCC k a (subst x e e')
            else subst x e alphaEq
   where
      alphaEq       = alphaConvertLetCC (LetCC k a e') usedVariables "\'"
      usedVariables = union (freeVariables e) (freeVariables e')
subst x e (Throw k e') = Throw (Prelude.map (subst x e) k) (subst x e e')

substStack :: String -> Stack -> Expr -> Expr 
substStack _ _ (Var y)      = Var y
substStack _ _ Taut         = Taut
substStack x e (Abort e' a) = Abort (substStack x e e') a
substStack x e (Lam y a e')
      | x == y = Lam y a e'
      |                                                                             -- The variable is bound, so we cannot perform the substitution
        otherwise = if notMember y (freeStackVariables e)
            then Lam y a (substStack x e e')                                        -- y is not a free variable of e, so we can perform the substitution
            else substStack x e alphaEq                                             -- y is a free variable of e, so we will perform the substitution on an alpha-equivalent expression
   where
      alphaEq       = alphaConvertLam (Lam y a e') usedVariables "\'"
      usedVariables = union (freeStackVariables e) (freeVariables e')               -- The free variables from e and e' cannot be used in determining the alpha-equivalent expression
substStack x e (App  e' e'') = App (substStack x e e') (substStack x e e'')
substStack x e (Pair e' e'') = Pair (substStack x e e') (substStack x e e'')
substStack x e (Fst e'     ) = Fst (substStack x e e')
substStack x e (Snd e'     ) = Snd (substStack x e e')
substStack x e (Inl e' a   ) = Inl (substStack x e e') a
substStack x e (Inr e' a   ) = Inr (substStack x e e') a
substStack x e vc@(VCase e' y e'' z e''') =
      case
                  ( notMember y (freeStackVariables e)
                  , notMember z (freeStackVariables e)
                  )
            of
                  (True, True) -> VCase (substStack x e e')
                                        y
                                        (substStack x e e'')
                                        z
                                        (substStack x e e''')                                        -- Neither y nor z are free variables of e
                  (True , False) -> substStack x e alphaEqRight                                      -- y is not a free variable of e, but z is
                  (False, True ) -> substStack x e alphaEqLeft                                       -- y is a free variable of e, but z isn't      
                  (False, False) -> substStack x e alphaEqBoth                                       -- y and z both are free variables of e 
   where
      alphaEqRight  = alphaConvertVCaseRight vc usedVarsRight "\'"
      usedVarsRight = union (freeStackVariables e) (freeVariables e''')
      alphaEqLeft   = alphaConvertVCaseLeft vc usedVarsLeft "\'"
      usedVarsLeft  = union (freeStackVariables e) (freeVariables e'')
      alphaEqBoth   = alphaConvertVCaseRight alphaEqLeft usedVarsRight "\'"
substStack x e (LetCC k a e')
      | x == k = LetCC k a e'
      | otherwise = if notMember k (freeStackVariables e)
            then LetCC k a (substStack x e e')
            else substStack x e alphaEq
   where
      alphaEq       = alphaConvertLetCC (LetCC k a e') usedVariables "\'"
      usedVariables = union (freeStackVariables e) (freeVariables e')
substStack x e (Throw k e') | k == stackVar x = Throw e (substStack x e e')
                            | otherwise =
      Throw (Prelude.map (substStack x e) k) (substStack x e e')


-- These functions convert different types of expressions into alpha-equivalent ones by adding apostrophes to the conflicting variable
alphaConvertLam :: Expr -> Set String -> String -> Expr
alphaConvertLam l@(Lam x a e) vars acc
      | notMember (x ++ acc) vars = Lam (x ++ acc)
                                        a
                                        (subst x (Var (x ++ acc)) e)
      | otherwise = alphaConvertLam l vars (acc ++ "\'")

alphaConvertVCaseLeft :: Expr -> Set String -> String -> Expr
alphaConvertVCaseLeft v@(VCase t x1 e1 x2 e2) vars acc
      | notMember (x1 ++ acc) vars = VCase t
                                           (x1 ++ acc)
                                           (subst x1 (Var (x1 ++ acc)) e1)
                                           x2
                                           e2
      | otherwise = alphaConvertVCaseLeft v vars (acc ++ "\'")

alphaConvertVCaseRight :: Expr -> Set String -> String -> Expr
alphaConvertVCaseRight v@(VCase t x1 e1 x2 e2) vars acc
      | notMember (x2 ++ acc) vars = VCase t
                                           x1
                                           e1
                                           (x2 ++ acc)
                                           (subst x2 (Var (x2 ++ acc)) e2)
      | otherwise = alphaConvertVCaseRight v vars (acc ++ "\'")

alphaConvertLetCC :: Expr -> Set String -> String -> Expr
alphaConvertLetCC l@(LetCC k a e) vars acc
      | notMember (k ++ acc) vars = LetCC (k ++ acc)
                                          a
                                          (subst k (Var (k ++ acc)) e)
      | otherwise = alphaConvertLetCC l vars (acc ++ "\'")

newVariable :: String -> Set String -> String -> String
newVariable x vars acc | notMember (x ++ acc) vars = x ++ acc
                       | otherwise = newVariable x vars (acc ++ "\'")

freeVariables :: Expr -> Set String
freeVariables (Var x             ) = singleton x
freeVariables (Taut              ) = S.empty
freeVariables (Abort e _         ) = freeVariables e
freeVariables (Lam x _ e         ) = S.delete x (freeVariables e)
freeVariables (App  e e'         ) = union (freeVariables e) (freeVariables e')
freeVariables (Pair e e'         ) = union (freeVariables e) (freeVariables e')
freeVariables (Fst e             ) = freeVariables e
freeVariables (Snd e             ) = freeVariables e
freeVariables (Inl e _           ) = freeVariables e
freeVariables (Inr e _           ) = freeVariables e
freeVariables (VCase e x e' y e'') = unions
      [ freeVariables e
      , S.delete x (freeVariables e')
      , S.delete y (freeVariables e'')
      ]    -- The variable x is bound in e', as is y in e''
freeVariables (LetCC k a e) = S.delete k (freeVariables e)
freeVariables (Throw k e  ) = union (freeStackVariables k) (freeVariables e)

freeStackVariables :: Stack -> Set String
freeStackVariables k = freeVariables (stackToExpr k (TVar "a"))


{- PROOFS -}
-- Program corresponding to the proof for : (-a \/ a) -> (--a -> a)
proofLemDne :: Expr
proofLemDne = Lam "t"
                  (Sum (notT (TVar "a")) (TVar "a"))
                  (VCase (Var "t") "l" s1 "r" s2)
   where
      s1 = Lam "x"
               (notT (notT (TVar "a")))
               (Abort (App (Var "x") (Var "l")) (TVar "a"))
      s2 = Lam "x" (notT (notT (TVar "a"))) (Fst (Pair (Var "r") (Var "x")))

-- Program corresponding to the proof for : (-a \/ a) -> ((-a -> a) -> a)
proofLemPeirce :: Expr
proofLemPeirce = Lam "t"
                     (Sum (notT (TVar "a")) (TVar "a"))
                     (VCase (Var "t") "l" s1 "r" s2)
   where
      s1 = Lam "x"
               (Func (notT (TVar "a")) (TVar "a"))
               (App (Var "x") (Var "l"))
      s2 = Lam "x"
               (Func (notT (TVar "a")) (TVar "a"))
               (Fst (Pair (Var "r") (Var "x")))
