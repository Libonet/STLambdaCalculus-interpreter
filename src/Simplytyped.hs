module Simplytyped
  ( conversion
  ,    -- conversion a terminos localmente sin nombre
    eval
  ,          -- evaluador
    infer
  ,         -- inferidor de tipos
    quote          -- valores -> terminos
  )
where

import           Data.List
import           Data.Maybe
import           Prelude                 hiding ( (>>=) )
import           Text.PrettyPrint.HughesPJ      ( render )
import           PrettyPrinter
import           Common

-----------------------
-- conversion
-----------------------

data BST a = BE | BN a Int (BST a) (BST a)

-- conversion a términos localmente sin nombres
conversion :: LamTerm -> Term
conversion t = conversion' t BE

conversion' :: LamTerm -> BST String -> Term
conversion' (LVar str) tree = let d = distance str tree
                              in if d /= -1 then Bound d else Free (Global str)
conversion' (LApp t1 t2) tree = (conversion' t1 tree) :@: (conversion' t2 tree)
conversion' (LAbs str typeName term) tree = let tree1 = increaseDistance tree
                                                tree2 = addTotree str tree1
                                            in Lam typeName (conversion' term tree2)
conversion' (LZero) tree = Zero
conversion' (LSuc t) tree = Suc (conversion' t tree)
conversion' (LRec t1 t2 t3) tree = Rec (conversion' t1 tree) (conversion' t2 tree) (conversion' t3 tree)
conversion' (LLet str t1 t2) tree = let tree1 = increaseDistance tree
                                        tree2 = addTotree str tree1
                                    in Let (conversion' t1 tree2) (conversion' t2 tree2)
conversion' (LNil) tree = Nil
conversion' (LCons t1 t2) tree = Cons (conversion' t1 tree) (conversion' t2 tree)
conversion' (LRecL t1 t2 t3) tree = RecL (conversion' t1 tree) (conversion' t2 tree) (conversion' t3 tree)


distance :: String -> BST String -> Int
distance str BE = -1
distance str (BN a d l r) | str < a = distance str l
                          | str > a = distance str r
                          | otherwise = d

addTotree :: String -> BST String -> BST String
addTotree str BE = (BN str 0 BE BE)
addTotree str (BN a d l r) | str < a = BN a d (addTotree str l) r
                           | str > a = BN a d l (addTotree str r)
                           | otherwise = BN a 0 l r

increaseDistance :: BST String -> BST String
increaseDistance BE = BE
increaseDistance (BN a d l r) = BN a (d+1) (increaseDistance l) (increaseDistance r)

----------------------------
--- evaluador de términos
----------------------------

-- substituye una variable por un término en otro término
sub :: Int -> Term -> Term -> Term
sub i t (Bound j) | i == j    = t
sub _ _ (Bound j) | otherwise = Bound j
sub _ _ (Free n   )           = Free n
sub i t (u   :@: v)           = sub i t u :@: sub i t v
sub i t (Zero)                = Zero
sub i t (Suc t')              = Suc (sub i t t')
sub i t (Rec t1 t2 t3)        = Rec (sub i t t1) (sub i t t2) (sub i t t3) 
sub i t (Lam t'  u)           = Lam t' (sub (i + 1) t u)
sub i t (Let t1 t2)           = Let (sub (i + 1) t t1) (sub (i + 1) t t2)
sub i t (Nil)                 = Nil
sub i t (Cons v t')           = Cons (sub i t v) (sub i t t')
sub i t (RecL t1 t2 t3)       = RecL (sub i t t1) (sub i t t2) (sub i t t3) 

-- convierte un valor en el término equivalente
quote :: Value -> Term
quote (VLam t f) = Lam t f
quote (VNum NZero) = Zero
quote (VNum (NSuc n)) = Suc (quote (VNum n))
quote (VList VNil) = Nil
quote (VList (VCons v l)) = Cons (quote (VNum v)) (quote (VList l))

-- evalúa un término en un entorno dado
eval :: NameEnv Value Type -> Term -> Value
eval (x:xs) (Free n)         = let (name, (v, _)) = x in if name == n then v else eval xs (Free n)
eval _ (Bound _)             = error "No se puede evaluar una variable ligada"
eval nvs (Lam dt t)          = VLam dt t
eval nvs (Zero)              = VNum NZero
eval nvs s@(Suc t)           = VNum (unrollSuc nvs s)
eval nvs (Rec t1 t2 Zero)    = eval nvs t1
eval nvs (Rec t1 t2 (Suc t)) = eval nvs ((t2 :@: (Rec t1 t2 t)) :@: t)
eval nvs (Rec t1 t2 t3)      = case eval nvs t3 of -- Esto se supone que tipo y por lo tatno no deberia no ser un numero. O sea este chequeo es innecesario
                                 VNum t -> eval nvs (Rec t1 t2 (quote (VNum t)))
                                 _      -> error "No se pudo evaluar Rec"
eval nvs (t1 :@: t2) = let v1 = eval nvs t1
                           v2 = eval nvs t2
                           Lam _ t1' = quote v1
                           t2' = quote v2
                       in eval nvs (sub 0 t2' t1')
eval nvs (Let t1 t2) = let v1 = eval nvs t1
                           t1' = quote v1
                       in eval nvs (sub 0 t1' t2)
eval nvs (Nil)        = VList VNil
eval nvs (Cons t1 t2) = let v1 = eval nvs t1
                            t2' = eval nvs t2
                        in case t2' of
                             VList t -> case v1 of
                                        VNum v -> VList $ VCons v t
                                        _      -> error "No se pudo evaluar Cons"
                             _       -> error "No se pudo evaluar Cons"
eval nvs (RecL t _ Nil) = eval nvs t
eval nvs (RecL t1 t2 (Cons n lv)) = eval nvs (t2 :@: n :@: lv :@: RecL t1 t2 lv)
eval nvs (RecL t1 t2 t3) = let t3' = quote $ eval nvs t3
                           in eval nvs (RecL t1 t2 t3')

{-
             | Nil
             | Cons Term Term
             | RecL Term Term Term
-}

unrollSuc :: NameEnv Value Type -> Term -> NumVal
unrollSuc nvs Zero    = NZero
unrollSuc nvs (Suc t) = NSuc (unrollSuc nvs t)
unrollSuc nvs t       = case eval nvs t of
                          VNum NZero     -> NZero
                          VNum (NSuc t') -> NSuc t'
                          _              -> error "No se pudo evaluar Suc"

----------------------
--- type checker
-----------------------

-- infiere el tipo de un término
infer :: NameEnv Value Type -> Term -> Either String Type
infer = infer' []

-- definiciones auxiliares
ret :: Type -> Either String Type
ret = Right

err :: String -> Either String Type
err = Left

(>>=)
  :: Either String Type -> (Type -> Either String Type) -> Either String Type
(>>=) v f = either Left f v
-- fcs. de error

matchError :: Type -> Type -> Either String Type
matchError t1 t2 =
  err
    $  "se esperaba "
    ++ render (printType t1)
    ++ ", pero "
    ++ render (printType t2)
    ++ " fue inferido."

notfunError :: Type -> Either String Type
notfunError t1 = err $ render (printType t1) ++ " no puede ser aplicado."

notfoundError :: Name -> Either String Type
notfoundError n = err $ show n ++ " no está definida."

-- infiere el tipo de un término a partir de un entorno local de variables y un entorno global
infer' :: Context -> NameEnv Value Type -> Term -> Either String Type
infer' c _ (Bound i) = ret (c !! i)
infer' _ e (Free  n) = case lookup n e of
  Nothing     -> notfoundError n
  Just (_, t) -> ret t
infer' c e (t :@: u) = infer' c e t >>= \tt -> infer' c e u >>= \tu ->
  case tt of
    FunT t1 t2 -> if (tu == t1) then ret t2 else matchError t1 tu
    _          -> notfunError tt
infer' c e (Lam t u) = infer' (t : c) e u >>= \tu -> ret $ FunT t tu
infer' c e Zero = ret NatT
infer' c e (Suc t) = infer' c e t >>= \tt -> if (tt == NatT) then ret NatT else matchError NatT tt
infer' c e (Rec t1 t2 t3) = infer' c e t1 >>= 
    \tt1 -> infer' c e t2 >>=
    \tt2 -> infer' c e t3 >>=
    \tt3 -> case tt3 of
              NatT -> case tt2 of
                        FunT t (FunT NatT t') -> if (t==tt1 && t'==tt1) 
                                                 then ret t
                                                 else matchError (FunT tt1 (FunT NatT tt1)) tt2
                        _                    -> matchError (FunT tt1 (FunT NatT tt1)) tt2
              _    -> matchError NatT tt3
infer' c e (Let t1 t2) = infer' c e t1 >>=
    \tt1 -> infer' (tt1 : c) e t2 >>=
      \tt2 -> ret tt2
infer' c e Nil = ret ListT
infer' c e (Cons t1 t2) = infer' c e t1 >>=
    \tt1 -> case tt1 of
              NatT -> infer' c e t2 >>= 
                      \tt2 -> case tt2 of 
                              ListT -> ret ListT
                              _     -> matchError ListT tt2
              _   -> matchError NatT tt1
infer' c e (RecL t1 t2 t3) = infer' c e t1 >>= 
    \tt1 -> infer' c e t2 >>=
    \tt2 -> infer' c e t3 >>=
    \tt3 -> case tt3 of
              ListT -> case tt2 of
                        FunT NatT (FunT ListT (FunT t t')) -> if t==tt1 && t'==tt1
                                                              then ret t
                                                              else matchError (FunT NatT (FunT ListT (FunT tt1 tt1))) tt2
                        _                    -> matchError (FunT NatT (FunT ListT (FunT tt1 tt1))) tt2
              _    -> matchError ListT tt3
