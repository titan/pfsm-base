module Pfsm.Parser

import Text.Lexer
import public Text.Parser.Core
import public Text.Parser
import Data.List

data Token = IInt Integer
           | Real Double
           | Identifier String
           | SString String
           | Comment String
           | OpenParen
           | CloseParen

export
Show Token where
  show (IInt i)       = "<int " ++ (show i) ++ ">"
  show (Real d)       = "<double " ++ (show d) ++ ">"
  show (Identifier i) = "<identifier " ++ i ++ ">"
  show (SString s)    = "<string " ++ s ++ ">"
  show (Comment c)    = "<comment " ++ c ++ ">"
  show OpenParen      = "("
  show CloseParen     = ")"

toInt' : String -> Integer
toInt' = cast

toDouble' : String -> Double
toDouble' = cast

comment : Lexer
comment = is ';' <+> is ';' <+> many (isNot '\n')

specialSymbol : Lexer
specialSymbol = oneOf "!$%&*/:<=>?^_~+-.@"

identifier : Lexer
identifier = (some (alphaNum <|> specialSymbol))

real : Lexer
real = digits <+> is '.' <+> digits

tokens : TokenMap Token
tokens =
  [ (real, \x => Real (toDouble' x))
  , (digits, \x => IInt (toInt' x ))
  , (identifier, Identifier)
  , (stringLit, SString)
  , (is '(', \x => OpenParen)
  , (is ')', \x => CloseParen)
  , (spaces, Comment)
  , (comment, Comment)
  ]

public export
data SExp = IntegerAtom Integer
          | RealAtom Double
          | SymbolAtom String
          | StringAtom String
          | SExpList (List SExp)

export
Show SExp where
  showPrec d (IntegerAtom n) = showCon d "IntegerAtom" $ showArg n
  showPrec d (RealAtom n)    = showCon d "RealAtom" $ showArg n
  showPrec d (SymbolAtom s)  = showCon d "SymbolAtom" $ showArg s
  showPrec d (StringAtom s)  = showCon d "StringAtom" $ showArg s
  showPrec d (SExpList l)    = showCon d "SExpList" $ showArg l


Rule : Type -> Type
Rule ty = Grammar (TokenData Token) True ty

intLit : Rule SExp
intLit
  = terminal "Expected integer literal"
             (\x => case tok x of
                         IInt n => Just (IntegerAtom n)
                         _ => Nothing)

realLit : Rule SExp
realLit
  = terminal "Expected real literal"
             (\x => case tok x of
                         Real n => Just (RealAtom n)
                         _ => Nothing)

idnLit : Rule SExp
idnLit
  = terminal "Expected identifier"
             (\x => case tok x of
                         Identifier i => Just (SymbolAtom i)
                         _ => Nothing)

strLit : Rule SExp
strLit
  = terminal "Expected string literal"
             (\x => case tok x of
                         SString s => case length s > 1 of
                                           True => Just (StringAtom (substr 1 (minus (length s) 2) s))
                                           False => Nothing
                         _ => Nothing)

openParen : Rule SExp
openParen
  = terminal "Expected open paren"
             (\x => case tok x of
                         OpenParen => Just (StringAtom "(")
                         _ => Nothing)

closeParen : Rule SExp
closeParen
  = terminal "Expected close paren"
             (\x => case tok x of
                         CloseParen => Just (StringAtom ")")
                         _ => Nothing)

sexp : Rule SExp
sexp = intLit
   <|> realLit
   <|> idnLit
   <|> strLit
   <|> do
       openParen
       xs <- many sexp
       closeParen
       pure (SExpList xs)

export
parseSExp : String -> Either (ParseError (TokenData Token)) (SExp, List (TokenData Token))
parseSExp inp
  = parse sexp (filter notComment (fst (lex tokens inp)))
  where
    notComment : TokenData Token -> Bool
    notComment t = case tok t of
                        Comment _ => False
                        _ => True
