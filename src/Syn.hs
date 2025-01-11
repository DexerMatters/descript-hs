module Syn where

import           GHC.Arr (Array, array)
import           Data.List (intercalate)

data Pattern = PAtom String
             | PTuple [Pattern]
             | PRecord [(String, Pattern)]
             | PAnnot Pattern TypeTerm
             | PWildcard
  deriving (Show)

data PrimitiveType = PrimInt
                   | PrimBool
                   | PrimUnit
                   | PrimString
  deriving (Eq)

instance Show PrimitiveType where
  show PrimInt = "int"
  show PrimBool = "bool"
  show PrimUnit = "()"
  show PrimString = "str"

data TypeTerm =
    TVar Int                     -- x
  | TPrimitive PrimitiveType     -- int, bool, unit, string
  | TArrow [TypeTerm] TypeTerm   -- (t1, t2, ..., tn) -> t
  | TTuple [TypeTerm]            -- (t1, t2, ..., tn)
  | TRecord [(String, TypeTerm)] -- { l1: t1, l2: t2, ..., ln: tn }
  | TApp TypeTerm [TypeTerm] [TypeTerm]     -- t<t1, t2, ..., tn>
  | TFree String
  | THole                        -- ?
    -- Intermediate types
  | TFix Int
  | TConv TypeTerm TypeTerm
  | TLam [Int] TypeTerm
  | TSeq [TypeTerm]
  | TLet Int TypeTerm TypeTerm

instance Show TypeTerm where
  show (TVar x) = "%" ++ show x
  show (TPrimitive l) = case l of
    PrimBool   -> "bool"
    PrimString -> "str"
    PrimInt    -> "int"
    PrimUnit   -> "()"
  show (TArrow tys ret) =
    "(" ++ intercalate "," (map show tys) ++ ") -> " ++ show ret
  show (TTuple tys) = "(" ++ intercalate "," (map show tys) ++ ")"
  show (TRecord fields) =
    "{" ++ intercalate "," (map (\(l, t) -> l ++ ": " ++ show t) fields) ++ "}"
  show (TApp t _ tys) = show t ++ "<" ++ intercalate "," (map show tys) ++ ">"
  show (TConv t1 t2) = show t1 ++ " => " ++ show t2
  show (TLam xs t) =
    "λ" ++ intercalate "," (map (\x -> "%" ++ show x) xs) ++ ". " ++ show t
  show (TSeq tys) = "{" ++ intercalate "," (map show tys) ++ "}"
  show (TFree s) = s
  show (TLet s t1 t2) =
    "let %" ++ show s ++ ": " ++ show t1 ++ " in " ++ show t2
  show THole = "_"
  show TFix {} = "fix"

data Literal = LInt Int
             | LBool Bool
             | LUnit
             | LString String
  deriving (Show)

data ExprTerm =
    -- | x
    Var String
    -- | 42
  | Lit Literal
    -- | (e1, e2, ..., en)
  | Tuple [ExprTerm]
    -- | { l1 = e1, l2 = e2, ..., ln = en }
  | Record [(String, ExprTerm)]
    -- | e.l
  | Proj ExprTerm String
    -- | (e1, e2, ..., en) => ret_type { body }
  | Fun { args :: [Pattern], ret_type :: Maybe TypeTerm, body :: ExprTerm }
    -- | f(e1, e2, ..., en)
  | App ExprTerm [ExprTerm]
    -- | let pat: t = rhs; body
  | Let { pat :: Pattern, rhs :: ExprTerm, body :: ExprTerm }
    -- | if (cond) then_branch else else_branch
  | If { cond :: ExprTerm, then_branch :: ExprTerm, else_branch :: ExprTerm }
    -- | { e1; e2; ...; en }
  | Seq [ExprTerm]
    -- | keyword e
  | Keyword String (Either ExprTerm TypeTerm)
    -- | type t = t'
  | TypeAlias { name :: String
              , poly :: Maybe [String]
              , ty :: TypeTerm
              , body :: ExprTerm
              }
  deriving (Show)

data Constr = Constr { tops :: [TypeTerm], bots :: [TypeTerm], locked :: Bool }
  deriving (Show)

pushTop :: TypeTerm -> Constr -> Constr
pushTop t c = c { tops = t:tops c }

pushBot :: TypeTerm -> Constr -> Constr
pushBot t c = c { bots = t:bots c }

newConstr :: Constr
newConstr = Constr [] [] False

lock :: Constr -> Constr
lock c = c { locked = True }

type ConstrEnv = Array Int (Maybe Constr)

initialConstrEnv :: ConstrEnv
initialConstrEnv = array (0, 1024) [(i, Nothing) | i <- [0 .. 1024]]