module Parser (parseExpr, parseProgram) where

import Text.Parsec
import Text.Parsec.String (Parser)
import Text.Parsec.Language (haskellStyle)
import Text.Parsec.Expr
import qualified Text.Parsec.Token as Token
import qualified Data.Set as Set

import Types

lexer:: Token.TokenParser ()
lexer = Token.makeTokenParser style
    where ops = ["->",".","\\","λ","+","-","*","=",":"]
          style = haskellStyle {
              Token.reservedOpNames = ops,
              Token.reservedNames = ["fun", "let", "rec", "in", "true", "false", "not", "and", "or", "then", "else"],
              Token.opStart = Token.opLetter style,
              Token.opLetter = oneOf "->.\\λ+-*=:"
          }

-- Generated lexers
reserved   = Token.reserved   lexer
reservedOp = Token.reservedOp lexer
identifier = Token.identifier lexer
parens     = Token.parens     lexer
natural    = Token.natural    lexer
braces     = Token.braces     lexer
commaSep1  = Token.commaSep1  lexer
semiSep1   = Token.semiSep1   lexer
symbol     = Token.symbol     lexer

parseExpr :: String -> Either ParseError Term
parseExpr = parse expr "Parser"

parseProgram :: String -> Either ParseError Program
parseProgram = parse program "Parser"

term :: Parser Term
term =  letExpr <|> abstraction <|> ifThenElse <|> apps

literal :: Parser Term
literal = Lit <$> natural

variable :: Parser Term
variable = Var <$> (identifier <|> try (symbol "true") <|> try (symbol "false"))

subtermNoSel :: Parser Term
subtermNoSel = parens term <|> record <|> literal <|> variable

subterm :: Parser Term
subterm = do
    st <- subtermNoSel
    sels <- many selection
    return $ foldl Sel st sels

subtermExtend :: Parser Term
subtermExtend = do
    st <- subtermNoSel
    sels <- many selection
    reservedOp "="
    Ext (foldl Sel st (init sels)) (last sels) <$> term

selection :: Parser Identifier
selection = do
    reservedOp "."
    identifier

record :: Parser Term
record = Rcd <$> braces members

members :: Parser [(Identifier, Term)]
members = do
    members <- semiSep1 member
    let labels = Set.fromList $ map fst members
    if Set.size labels == length members
        then return members
        else unexpected "Record contains duplicate labels"

member :: Parser (Identifier, Term)
member = do
    name <- identifier
    reservedOp "="
    value <- term
    return (name, value)

abstraction :: Parser Term
abstraction = do
    lambdaToken
    args <- many1 identifier
    absToken
    body <- term
    return $ foldr Lam body args

letExpr :: Parser Term
letExpr = do
    reserved "let"
    isRec <- option False (do {reserved "rec"; return True})
    name <- identifier
    reservedOp "="
    value <- term
    reserved "in"
    Let isRec name value <$> term

ifThenElse :: Parser Term
ifThenElse = do
    reserved "if"
    e1 <- term
    reserved "then"
    e2 <- term
    reserved "else"
    App (App (App (Var "if") e1) e2) <$> term

apps :: Parser Term
apps = do
    terms <- many1 (try subtermExtend <|> subterm)
    return $ foldl1 App terms

definition :: Parser Definition
definition = do
    reserved "let"
    isRec <- option False (do {reserved "rec"; return True})
    name <- identifier
    reservedOp "="
    e <- term    
    return (isRec, name, e)

expr :: Parser Term
expr = do
    Token.whiteSpace lexer
    e <- term
    eof
    return e

program :: Parser Program
program = do
    Token.whiteSpace lexer
    definitions <- many definition
    eof
    return definitions

-- Operator lexers
lambdaToken :: Parser ()
lambdaToken =  reservedOp "\\"
           <|> reservedOp "λ"
           <|> reserved "fun"

absToken :: Parser ()
absToken =  reservedOp "->"