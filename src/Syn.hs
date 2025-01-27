
module Syn where

import           GHC.Arr (Array, array)
import           Data.List (intercalate)
import           GHC.Base (maxInt)

data BinOp = BinOp { binOpSign :: String
                   , binOpName :: String
                   , binOpPrec :: Int
                   , binOpAssoc :: Assoc
                   }
  deriving (Eq)

instance Show BinOp where
  show = binOpSign

data Assoc = AssocLeft
           | AssocRight
           | AssocNone
  deriving (Eq, Show)

operatorTable :: [BinOp]
operatorTable =
  [ BinOp "&&" "and" 1 AssocLeft
  , BinOp "||" "or" 2 AssocLeft
  , BinOp "<" "lt" 3 AssocNone
  , BinOp "<=" "le" 3 AssocNone
  , BinOp ">" "gt" 3 AssocNone
  , BinOp ">=" "ge" 3 AssocNone
  , BinOp "+" "add" 4 AssocLeft
  , BinOp "-" "sub" 4 AssocLeft
  , BinOp "*" "mul" 5 AssocLeft
  , BinOp "/" "div" 5 AssocLeft
  , BinOp "%" "mod" 5 AssocLeft
    -- Most precedence
  , BinOp "EOT" "EOT" maxInt AssocNone]

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
  show (TFix n) = "fix " ++ show n

data Literal = LInt Int
             | LBool Bool
             | LUnit
             | LString String
  deriving (Show)

data Statement =
    -- | function f(x1, x2, ..., xn) { body }
    -- | function f(x1, x2, ..., xn): t { body }
    FunDecl String [Pattern] (Maybe TypeTerm) ExprTerm
    -- | let x = e
    -- | let x: t = e
  | LetDecl String (Maybe TypeTerm) ExprTerm
    -- | type t = t'
    -- | type t<x1, x2, ..., xn> = t'
  | TypeDecl String (Maybe [String]) TypeTerm
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
    -- | (e1, e2, ..., en) => e
    -- | (e1, e2, ..., en) t => e
  | Fun [Pattern] (Maybe TypeTerm) ExprTerm
    -- | e1(e2, e3, ..., en)
  | App ExprTerm [ExprTerm]
    -- | let x = e1; e2
  | Let Pattern ExprTerm ExprTerm
    -- | if (e1) e2 else e3
  | If ExprTerm ExprTerm ExprTerm
    -- | { e1; e2; ...; en }
  | Seq [ExprTerm]
    -- | keyword e
  | Keyword String (Either ExprTerm TypeTerm)
    -- | type t = t'; body
    -- | type t<x1, x2, ..., xn> = t'; body
  | TypeAlias { name :: String
              , poly :: Maybe [String]
              , ty :: TypeTerm
              , body :: ExprTerm
              }
    -- Special cases
  | Native
  deriving (Show)

