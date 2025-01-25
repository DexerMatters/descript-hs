{-# LANGUAGE LambdaCase #-}

module Parser where

import           Text.Megaparsec (choice, manyTill, anySingle, Parsec, between
                                , sepBy, MonadParsec(try, eof), optional)
import           Syn (Literal(..), ExprTerm(..), Pattern(..), TypeTerm(..)
                    , PrimitiveType(..), Statement(..))
import           GHC.Base (Alternative(..))
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import           Data.Void (Void)
import           Data.Functor (($>))

type Parser = Parsec Void String

preserved :: [String]
preserved =
  ["true", "false", "int", "bool", "if", "else", "let", "function", "check"]

ws :: Parser ()
ws = L.space space1 (L.skipLineComment "//") (L.skipBlockComment "/*" "*/")

lexeme :: Parser String -> Parser String
lexeme = L.lexeme ws

symbol :: String -> Parser String
symbol = L.symbol ws

ident :: Parser String
ident = do
  x <- lexeme $ (:) <$> letterChar <*> many alphaNumChar
  if x `elem` preserved
    then fail $ "Identifier " ++ x ++ " is preserved"
    else pure x

typeIdent :: Parser String
typeIdent = lexeme $ (:) <$> upperChar <*> many alphaNumChar

sepBy2 :: Parser a -> Parser b -> Parser [a]
sepBy2 a b = do
  first <- a
  rest <- some $ b *> a
  pure $ first:rest

parseLiteral :: Parser Literal
parseLiteral = choice
  [ LInt . read <$> lexeme (some digitChar)
  , LBool True <$ symbol "true"
  , LBool False <$ symbol "false"
  , LUnit <$ string "unit"
  , LString <$> lexeme (char '"' *> manyTill anySingle (char '"'))]

-- | Top-level parser

parseProgram :: Parser [Statement]
parseProgram = manyTill parseStatement eof

-- | Statement parser

parseStatement :: Parser Statement
parseStatement = choice [parseFunDecl, parseLetDecl, parseTypeDecl]

parseFunDecl :: Parser Statement
parseFunDecl = FunDecl <$> (symbol "function" *> ident)
  <*> between (symbol "(") (symbol ")") (parsePattern 0 `sepBy` symbol ",")
  <*> optional (symbol ":" *> parseTypeTerm 0)
  <*> (symbol "{" *> allowedAll <* symbol "}")

parseLetDecl :: Parser Statement
parseLetDecl = LetDecl <$> (symbol "let" *> ident)
  <*> optional (symbol ":" *> parseTypeTerm 0)
  <*> (symbol "=" *> allowedBody)

parseTypeDecl :: Parser Statement
parseTypeDecl = TypeDecl <$> (symbol "type" *> typeIdent)
  <*> optional
    (between (symbol "<") (symbol ">") $ typeIdent `sepBy` symbol ",")
  <*> (symbol "=" *> parseTypeTerm 0)

-- | Expression parser


parseParen :: Parser ExprTerm
parseParen = between (symbol "(") (symbol ")") allowedAll

parseVariable :: Parser ExprTerm
parseVariable = Var <$> ident

parseTuple :: Parser ExprTerm
parseTuple = do
  elems <- between (symbol "(") (symbol ")") $ allowedInArg `sepBy2` symbol ","
  pure $ Tuple elems

parseLiteralExpr :: Parser ExprTerm
parseLiteralExpr = Lit <$> parseLiteral

parseRecord :: Parser ExprTerm
parseRecord = Record
  <$> between (symbol "{") (symbol "}") (parseField `sepBy` symbol ",")
  where
    parseField = (,) <$> ident <*> (symbol "=" *> allowedBody)

parseFunction :: Parser ExprTerm
parseFunction = Fun
  <$> between (symbol "(") (symbol ")") (parsePattern 0 `sepBy` symbol ",")
  <*> optional (parseTypeTerm 0)
  <*> (symbol "=>" *> allowedBody)

parseApp :: Parser ExprTerm
parseApp = do
  first <- allowedApp
  rest <- some
    $ between (symbol "(") (symbol ")") (allowedInArg `sepBy` symbol ",")
  pure $ foldl App first rest

parseIf :: Parser ExprTerm
parseIf = If
  <$> (symbol "if" *> between (symbol "(") (symbol ")") allowedInArg)
  <*> allowedBody
  <*> (symbol "else" *> allowedBody)

parseLet :: Parser ExprTerm
parseLet = Let <$> (symbol "let" *> parsePattern 0)
  <*> (symbol "=" *> allowedBody)
  <*> (symbol ";" *> allowedAll)

parseTypeAlias :: Parser ExprTerm
parseTypeAlias = TypeAlias <$> (symbol "type" *> ident)
  <*> optional
    (between (symbol "<") (symbol ">") $ typeIdent `sepBy` symbol ",")
  <*> (symbol "=" *> parseTypeTerm 0)
  <*> (symbol ";" *> allowedAll)

parseProj :: Parser ExprTerm
parseProj = do
  first <- allowedProj
  path <- some $ symbol "." *> ident
  pure $ foldl Proj first path

parseSequence :: Parser ExprTerm
parseSequence = Seq
  <$> between (symbol "{") (symbol "}") (allowedAll `sepBy` symbol ";")

parseKeywords :: Parser ExprTerm
parseKeywords = choice
  [Keyword "check" . Right <$> (symbol "check" *> parseTypeTerm 0)]

-- | Type parser

parseTypeTerm :: Int -> Parser TypeTerm
parseTypeTerm priority = choice
  $ drop priority
  $ try
  <$> [ try parseAppType
      , parseFunctionType
      , parseRecordType
      , parseTupleType
      , parseHoleType
      , parseFreeType
      , parsePrimitiveType
      , parseTypeParen]

parseTypeParen :: Parser TypeTerm
parseTypeParen = between (symbol "(") (symbol ")") $ parseTypeTerm 0

parsePrimitiveType :: Parser TypeTerm
parsePrimitiveType = TPrimitive
  <$> choice
    [ symbol "int" $> PrimInt
    , symbol "bool" $> PrimBool
    , symbol "unit" $> PrimUnit
    , symbol "str" $> PrimString]

parseTupleType :: Parser TypeTerm
parseTupleType = TTuple
  <$> between (symbol "(") (symbol ")") (parseTypeTerm 0 `sepBy` symbol ",")

parseRecordType :: Parser TypeTerm
parseRecordType = TRecord
  <$> between (symbol "{") (symbol "}") (parseField `sepBy` symbol ",")
  where
    parseField = (,) <$> ident <*> (symbol ":" *> parseTypeTerm 0)

parseFunctionType :: Parser TypeTerm
parseFunctionType = TArrow
  <$> between (symbol "(") (symbol ")") (parseTypeTerm 0 `sepBy` symbol ",")
  <*> (symbol "->" *> parseTypeTerm 0)

parseFreeType :: Parser TypeTerm
parseFreeType = TFree <$> typeIdent

parseHoleType :: Parser TypeTerm
parseHoleType = THole <$ symbol "?"

parseAppType :: Parser TypeTerm
parseAppType = TApp <*> pure [] <$> parseTypeTerm 2
  <*> between (symbol "<") (symbol ">") (parseTypeTerm 0 `sepBy` symbol ",")

-- | Pattern parser
parsePattern :: Int -> Parser Pattern
parsePattern priority = choice
  $ drop priority
  $ try
  <$> [ parseAnnotPattern
      , parseRecordPattern
      , parseTuplePattern
      , parseWildcardPattern
      , parseAtomPattern]

parseAtomPattern :: Parser Pattern
parseAtomPattern = PAtom <$> ident

parseTuplePattern :: Parser Pattern
parseTuplePattern = do
  elems <- between (symbol "(") (symbol ")")
    $ parsePattern 0 `sepBy` symbol ","
  pure $ PTuple elems

parseRecordPattern :: Parser Pattern
parseRecordPattern = do
  elems <- between (symbol "{") (symbol "}") $ parseField `sepBy` symbol ","
  pure $ PRecord elems
  where
    parseField = (,) <$> ident <*> (symbol "=" *> parsePattern 0)

parseAnnotPattern :: Parser Pattern
parseAnnotPattern = PAnnot <$> parsePattern 1
  <*> (symbol ":" *> parseTypeTerm 0)

parseWildcardPattern :: Parser Pattern
parseWildcardPattern = PWildcard <$ symbol "_"

-- | Priority table

allExpr :: [Parser ExprTerm]
allExpr = try
  <$> [ parseLet        -- 0
      , parseTypeAlias  -- 1
      , parseKeywords   -- 2
      , parseSequence   -- 3
      , parseFunction   -- 4
      , parseIf         -- 5
      , parseRecord     -- 6
      , parseTuple      -- 7
      , parseProj       -- 8
      , parseApp        -- 9
      , parseLiteralExpr -- 10
      , parseVariable  -- 11
      , parseParen     -- 12
      ]

allowedInArg :: Parser ExprTerm
allowedInArg = choice $ (allExpr !!) <$> [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

allowedProj :: Parser ExprTerm
allowedProj = choice $ (allExpr !!) <$> [3, 6, 7, 10, 11, 12]

allowedApp :: Parser ExprTerm
allowedApp = choice $ (allExpr !!) <$> [3, 6, 7, 10, 11, 12]

allowedBody :: Parser ExprTerm
allowedBody = choice $ (allExpr !!) <$> [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

allowedAll :: Parser ExprTerm
allowedAll = choice allExpr
