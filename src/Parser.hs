{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Parser where

import Data.Foldable (Foldable (fold))
import Data.Functor (($>))
import Data.Void (Void)
import GHC.Base (Alternative (..))
import Syn
  ( BinOp (..),
    ExprTerm (..),
    ExprTerm',
    Literal (..),
    Pattern (..),
    Pattern',
    PrimitiveType (..),
    TypeDescriptor (..),
    TypePattern (..),
    TypePattern',
    TypeTerm (..),
    TypeTerm',
    operatorTable,
  )
import Text.Megaparsec
  ( MonadParsec (eof, try),
    Parsec,
    anySingle,
    between,
    choice,
    getOffset,
    manyTill,
    optional,
    sepBy,
  )
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Utils (FI (..), WithFI (..), type ($))

type Parser = Parsec Void String

preserved :: [String]
preserved =
  [ "true",
    "false",
    "int",
    "bool",
    "if",
    "else",
    "let",
    "function",
    "check",
    "native"
  ]

ws :: Parser ()
ws = L.space space1 (L.skipLineComment "//") (L.skipBlockComment "/*" "*/")

withFI :: Parser a -> Parser (WithFI a)
withFI p = do
  start <- getOffset
  v <- p
  end <- getOffset
  pure $ WithFI (FI "" start end) v

withFI' :: Parser (WithFI a) -> Parser (WithFI a)
withFI' p = do
  start <- getOffset
  WithFI _ v <- p
  end <- getOffset
  pure $ WithFI (FI "" start end) v

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
  pure $ first : rest

parseLiteral :: Parser Literal
parseLiteral =
  choice
    [ LInt . read <$> lexeme (some digitChar),
      LBool True <$ symbol "true",
      LBool False <$ symbol "false",
      LUnit <$ string "unit",
      LString <$> lexeme (char '"' *> manyTill anySingle (char '"'))
    ]

binOp :: WithFI BinOp -> ExprTerm' -> ExprTerm' -> ExprTerm'
binOp op a b =
  WithFI (fi a <> fi b) $
    App (WithFI (fi op) $ Var (binOpName (val op))) [a, b]

-- | Top-level parser

-- parseProgram :: Parser [Statement]
-- parseProgram = manyTill parseStatement eof

-- -- | Statement parser

-- parseStatement :: Parser Statement
-- parseStatement =
--   choice [parseFunDecl, parseLetDecl, parseTypeDecl, parseEnumDecl]

-- parseFunDecl :: Parser Statement
-- parseFunDecl = FunDecl <$> (symbol "function" *> ident)
--   <*> between (symbol "(") (symbol ")") (parsePattern 0 `sepBy` symbol ",")
--   <*> optional (symbol ":" *> parseTypeTerm 0)
--   <*> ((symbol "-- native" $> Native)
--        <|> (symbol "{" *> allowedAll <* symbol "}"))

-- parseLetDecl :: Parser Statement
-- parseLetDecl = LetDecl <$> (symbol "let" *> ident)
--   <*> optional (symbol ":" *> parseTypeTerm 0)
--   <*> (symbol "=" *> allowedBody)

-- parseTypeDecl :: Parser Statement
-- parseTypeDecl = TypeDecl <$> (symbol "type" *> typeIdent)
--   <*> optional
--     (between (symbol "<") (symbol ">") $ typeIdent `sepBy` symbol ",")
--   <*> (symbol "=" *> parseTypeTerm 0)

-- parseEnumDecl :: Parser Statement
-- parseEnumDecl = EnumDecl <$> (symbol "enum" *> typeIdent)
--   <*> optional
--     (between (symbol "<") (symbol ">") $ typeIdent `sepBy` symbol ",")
--   <*> (symbol "{" *> parseEnumVariant `sepBy` symbol "," <* symbol "}")
--   where
--     parseEnumVariant = (,) <$> ident
--       <*> fmap
--         (concat . toList)
--         (optional
--            (between (symbol "(") (symbol ")")
--             $ parseTypeTerm 0 `sepBy` symbol ","))

-- | Expression parser
parseParen :: Parser ExprTerm'
parseParen = withFI' $ between (symbol "(") (symbol ")") allowedAll

parseVariable :: Parser ExprTerm'
parseVariable = withFI $ Var <$> ident

parsePolyApp :: Parser $ ExprTerm'
parsePolyApp =
  withFI $
    App'
      <$> allowedApp
      <*> between (symbol "<") (symbol ">") (parseTypeTerm 0 `sepBy` symbol ",")

parseTuple :: Parser ExprTerm'
parseTuple = withFI $
  do
    elems <-
      between (symbol "(") (symbol ")") $
        allowedInArg `sepBy2` symbol ","
    pure $ Tuple elems

parseLiteralExpr :: Parser ExprTerm'
parseLiteralExpr = withFI $ Lit <$> parseLiteral

parseBinaryOp :: BinOp -> Parser ExprTerm'
parseBinaryOp op =
  withFI' $
    do
      sepBy2 allowedArith (withFI $ symbol $ binOpSign op)
      >>= \case
        [x] -> pure x
        (x : xs) -> pure $ foldl (binOp (WithFI (FI "" 0 0) op)) x xs
        _ -> fail "impossible"

parseRecord :: Parser ExprTerm'
parseRecord =
  withFI $
    Record
      <$> between (symbol "{") (symbol "}") (parseField `sepBy` symbol ",")
  where
    parseField = (,) <$> ident <*> (symbol "=" *> allowedBody)

parseFunction :: Parser ExprTerm'
parseFunction =
  withFI $
    Fun
      <$> between (symbol "(") (symbol ")") (parsePattern 0 `sepBy` symbol ",")
      <*> optional (parseTypeTerm 0)
      <*> (symbol "=>" *> allowedBody)

parseApp :: Parser ExprTerm'
parseApp = withFI' $
  do
    first <- allowedApp
    rest <-
      some $
        between (symbol "(") (symbol ")") (allowedInArg `sepBy` symbol ",")
    pure $ foldl (\a b -> WithFI (fold $ fi a : fmap fi b) $ App a b) first rest

parseIf :: Parser ExprTerm'
parseIf =
  withFI $
    If
      <$> (symbol "if" *> between (symbol "(") (symbol ")") allowedInArg)
      <*> allowedBody
      <*> (symbol "else" *> allowedBody)

parseLet :: Parser ExprTerm'
parseLet =
  withFI $
    Let
      <$> (symbol "let" *> parsePattern 0)
      <*> (symbol "=" *> allowedBody)
      <*> (symbol ";" *> (allowedAll <|> withFI (eof $> Lit LUnit)))

parseTypeAlias :: Parser ExprTerm'
parseTypeAlias =
  withFI $
    TypeAlias
      <$> (symbol "type" *> ident)
      <*> optional
        (between (symbol "<") (symbol ">") $ parseTypePattern 0 `sepBy` symbol ",")
      <*> (symbol "=" *> parseTypeTerm 0)
      <*> (symbol ";" *> (allowedAll <|> withFI (eof $> Lit LUnit)))

parseProj :: Parser ExprTerm'
parseProj = withFI' $
  do
    first <- allowedProj
    path <- some $ symbol "." *> ident
    pure $ foldl (\a b -> WithFI (fi a) $ Proj a b) first path

parseSequence :: Parser ExprTerm'
parseSequence =
  withFI $
    Seq
      <$> between
        (symbol "{")
        (symbol "}")
        ( (allowedAll <|> withFI (eof $> Lit LUnit))
            `sepBy` symbol ";"
        )

parseKeywords :: Parser ExprTerm'
parseKeywords =
  withFI $
    choice [Keyword "check" . Right <$> (symbol "check" *> parseTypeTerm 0)]

parseForall :: Parser ExprTerm'
parseForall =
  withFI $
    Forall
      <$> ( symbol "with"
              *> between
                (symbol "<")
                (symbol ">")
                (parseTypePattern 0 `sepBy` symbol ",")
          )
      <*> allowedBody

-- | Type parser
parseTypeTerm :: Int -> Parser TypeTerm'
parseTypeTerm priority =
  choice $
    drop priority $
      try
        <$> [ try parseAppType,
              try parseProjType,
              parseFunctionType,
              parseRecordType,
              parseTupleType,
              parseHoleType,
              parseFreeType,
              parsePrimitiveType,
              parseTypeParen
            ]

parseTypeParen :: Parser TypeTerm'
parseTypeParen = withFI' $ between (symbol "(") (symbol ")") $ parseTypeTerm 0

parsePrimitiveType :: Parser TypeTerm'
parsePrimitiveType =
  withFI $
    TPrimitive
      <$> choice
        [ symbol "int" $> PrimInt,
          symbol "bool" $> PrimBool,
          symbol "unit" $> PrimUnit,
          symbol "str" $> PrimString
        ]

parseTupleType :: Parser TypeTerm'
parseTupleType =
  withFI $
    TTuple
      <$> between (symbol "(") (symbol ")") (parseTypeTerm 0 `sepBy` symbol ",")

parseRecordType :: Parser TypeTerm'
parseRecordType =
  withFI $
    TRecord
      <$> between (symbol "{") (symbol "}") (parseField `sepBy` symbol ",")
  where
    parseField = (,) <$> ident <*> (symbol ":" *> parseTypeTerm 0)

parseFunctionType :: Parser TypeTerm'
parseFunctionType =
  withFI $
    TArrow
      <$> between (symbol "(") (symbol ")") (parseTypeTerm 0 `sepBy` symbol ",")
      <*> (symbol "->" *> parseTypeTerm 0)

parseFreeType :: Parser TypeTerm'
parseFreeType = withFI $ TVar <$> typeIdent

parseHoleType :: Parser TypeTerm'
parseHoleType = withFI $ THole <$ symbol "?"

parseAppType :: Parser TypeTerm'
parseAppType =
  withFI $
    TApp
      <$> parseTypeTerm 3
      <*> between (symbol "<") (symbol ">") (parseTypeTerm 0 `sepBy` symbol ",")

parseProjType :: Parser TypeTerm'
parseProjType = withFI' $
  do
    first <- parseTypeTerm 3
    path <- some $ symbol "." *> ident
    pure $ foldl (\a b -> WithFI (fi a) $ TProj a b) first path

-- | Pattern parser
parsePattern :: Int -> Parser Pattern'
parsePattern priority =
  choice $
    drop priority $
      try
        <$> [ parseAnnotPattern,
              parseRecordPattern,
              parseTuplePattern,
              parseWildcardPattern,
              parseAtomPattern
            ]

parseAtomPattern :: Parser Pattern'
parseAtomPattern = withFI $ PAtom <$> ident

parseTuplePattern :: Parser Pattern'
parseTuplePattern = withFI $
  do
    elems <-
      between (symbol "(") (symbol ")") $
        parsePattern 0 `sepBy` symbol ","
    pure $ PTuple elems

parseRecordPattern :: Parser Pattern'
parseRecordPattern = withFI $
  do
    elems <- between (symbol "{") (symbol "}") $ parseField `sepBy` symbol ","
    pure $ PRecord elems
  where
    parseField = (,) <$> ident <*> (symbol "=" *> parsePattern 0)

parseAnnotPattern :: Parser Pattern'
parseAnnotPattern =
  withFI $
    PAnnot <$> parsePattern 1 <*> (symbol ":" *> parseTypeTerm 0)

parseWildcardPattern :: Parser Pattern'
parseWildcardPattern = withFI $ PWildcard <$ symbol "_"

-- | Type Pattern parser
parseTypePattern :: Int -> Parser TypePattern'
parseTypePattern priority =
  choice $
    drop priority $
      try <$> [parseTRecordPattern, parseTTuplePattern, parseTAtomPattern]

parseTAtomPattern :: Parser TypePattern'
parseTAtomPattern =
  withFI $
    choice
      [ try $ TPAtom <$> (symbol "flex" $> Flexible) <*> typeIdent,
        TPAtom Rigid <$> typeIdent
      ]

parseTTuplePattern :: Parser TypePattern'
parseTTuplePattern = withFI $
  do
    elems <-
      between (symbol "(") (symbol ")") $
        parseTypePattern 0 `sepBy` symbol ","
    pure $ TPTuple elems

parseTRecordPattern :: Parser TypePattern'
parseTRecordPattern = withFI $
  do
    elems <- between (symbol "{") (symbol "}") $ parseField `sepBy` symbol ","
    pure $ TPRecord elems
  where
    parseField = (,) <$> ident <*> (symbol ":" *> parseTypePattern 0)

-- | Priority table
allExpr :: [Parser ExprTerm']
allExpr =
  try
    <$> [ parseLet, -- 0
          parseTypeAlias, -- 1
          parseKeywords, -- 2
          parseSequence, -- 3
          parseForall, -- 4
          parseFunction, -- 5
          parseIf, -- 6
          parseRecord, -- 7
          parseTuple, -- 8
          parseProj, -- 9
          parseBinaryOp (operatorTable !! 6), -- 10
          parseApp, -- 11
          parsePolyApp, -- 12
          parseLiteralExpr, -- 13
          parseVariable, -- 14
          parseParen -- 15
        ]

allowedInArg :: Parser ExprTerm'
allowedInArg =
  choice $
    (allExpr !!) <$> [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

allowedProj :: Parser ExprTerm'
allowedProj = choice $ (allExpr !!) <$> [3, 6, 7, 12, 13, 14, 15]

allowedApp :: Parser ExprTerm'
allowedApp = choice $ (allExpr !!) <$> [3, 6, 7, 13, 14, 15]

allowedBody :: Parser ExprTerm'
allowedBody =
  choice $
    (allExpr !!) <$> [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]

allowedArith :: Parser ExprTerm'
allowedArith = choice $ (allExpr !!) <$> [3, 6, 7, 8, 11, 12, 13, 14, 15]

allowedAll :: Parser ExprTerm'
allowedAll = choice allExpr
