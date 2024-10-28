module PrettyPrinter
  ( printTerm  ,     -- pretty printer para terminos
    printType        -- pretty printer para tipos
  )
where

import  Common
import  Text.PrettyPrint.HughesPJ
import  Prelude hiding ((<>))

-- lista de posibles nombres para variables
vars :: [String]
vars =
  [ c : n
  | n <- "" : map show [(1 :: Integer) ..]
  , c <- ['x', 'y', 'z'] ++ ['a' .. 'w']
  ]

parensIf :: Bool -> Doc -> Doc
parensIf True  = parens
parensIf False = id

-- pretty-printer de términos

pp :: Int -> [String] -> Term -> Doc
pp ii vs (Bound k         ) = text (vs !! (ii - k - 1))
pp _  _  (Free  (Global s)) = text s

pp ii vs (i :@: c         ) = sep
  [ parensIf (isLam i) (pp ii vs i)
  , nest 1 (parensIf (isLam c || isApp c) (pp ii vs c))
  ]
pp ii vs (Lam t c) =
  text "\\"
    <> text (vs !! ii)
    <> text ":"
    <> printType t
    <> text ". "
    <> pp (ii + 1) vs c
pp ii vs (Zero)  = text "0"
pp ii vs s@(Suc t) = let (n, doc, kind) = fromSucToInt ii vs s
                     in case kind of
                          "0"   -> text (show n)
                          "var" -> text (show n) <> text "+" <> doc
                          _     -> text (show n) <> text "+" <> parens doc
pp ii vs (Rec t1 t2 t3) = 
  text "R "
    <+> parens (pp ii vs t1)
    <+> parens (pp ii vs t2)
    <+> parens (pp ii vs t3)
pp ii vs (Let t1 t2) = text "let" <+> text (vs !! ii) <> text "=" <> pp (ii + 1) vs t1 <+> text "in" <+> pp (ii + 1) vs t2
pp ii vs (Nil) = text "[]"
pp ii vs c@(Cons v t) = text "[" <> unrollCons ii vs c <> text "]"

unrollCons ii vs (Nil)        = empty
unrollCons ii vs (Cons v Nil) = pp ii vs v
unrollCons ii vs (Cons v t)   = pp ii vs v <> text "," <+> unrollCons ii vs t
unrollCons ii vs t            = pp ii vs t

fromSucToInt :: Int -> [String] -> Term -> (Int, Doc, String)
fromSucToInt ii vs Zero      = (0, text "0", "0")
fromSucToInt ii vs (Bound k) = (0, text (vs !! (ii - k - 1)), "var")
fromSucToInt ii vs (Suc t)   = let (n, doc, str) = fromSucToInt ii vs t
                               in (1+n, doc, str)
fromSucToInt ii vs t         = (0, pp ii vs t, "other")


isLam :: Term -> Bool
isLam (Lam _ _) = True
isLam _         = False

isApp :: Term -> Bool
isApp (_ :@: _) = True
isApp _         = False

-- pretty-printer de tipos
printType :: Type -> Doc
printType EmptyT = text "E"
printType NatT   = text "Nat"
printType ListT  = text "List"
printType (FunT t1 t2) =
  sep [parensIf (isFun t1) (printType t1), text "->", printType t2]


isFun :: Type -> Bool
isFun (FunT _ _) = True
isFun _          = False

fv :: Term -> [String]
fv (Bound _         ) = []
fv (Free  (Global n)) = [n]
fv (Zero) = []
fv (Suc n) = fv n
fv (Rec t1 t2 t3) = fv t1 ++ fv t2 ++ fv t3
fv (t   :@: u       ) = fv t ++ fv u
fv (Lam _   u       ) = fv u
fv (Let t1 t2) = fv t1 ++ fv t2
--fv (Nil) = []
--fv (Cons v t1) = fv v ++ fv t1
fv _ = ["Me olvide de un caso uwu"]

---
printTerm :: Term -> Doc
printTerm t = pp 0 (filter (\v -> not $ elem v (fv t)) vars) t

