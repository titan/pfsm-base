module Pfsm.Parser

import Text.Lexer
import public Text.Parser.Core
import public Text.Parser
import Data.List

data FsmKind = FKInt | FKReal | FKIdentifier | FKChar | FKString | FKComment | FKOpenParen | FKCloseParen

TokenKind FsmKind where
  TokType  FKInt          = Int
  TokType  FKReal         = Double
  TokType  FKIdentifier   = String
  TokType  FKChar         = Char
  TokType  FKString       = String
  TokType  FKComment      = String
  TokType  FKOpenParen    = ()
  TokType  FKCloseParen   = ()
  tokValue FKInt x        = cast x
  tokValue FKReal x       = cast x
  tokValue FKIdentifier x = x
  tokValue FKChar x       = case unpack(x) of
                                 '\'' :: '\\' :: 'a' :: '\'' :: [] => '\a'
                                 '\'' :: '\\' :: 'b' :: '\'' :: [] => '\b'
                                 '\'' :: '\\' :: 'f' :: '\'' :: [] => '\f'
                                 '\'' :: '\\' :: 'n' :: '\'' :: [] => '\n'
                                 '\'' :: '\\' :: 'r' :: '\'' :: [] => '\r'
                                 '\'' :: '\\' :: 't' :: '\'' :: [] => '\t'
                                 '\'' :: '\\' :: 'v' :: '\'' :: [] => '\v'
                                 '\'' :: '\\' :: '\\' :: '\'' :: [] => '\\'
                                 '\'' :: c :: '\'' :: [] => c
                                 _ => '\0'
  tokValue FKString x     = case length x > 1 of
                                 True => (substr 1 (minus (length x) 2) x)
                                 _ => ""
  tokValue FKComment x    = x
  tokValue FKOpenParen x  = ()
  tokValue FKCloseParen x = ()

Eq FsmKind where
  (==) FKInt        FKInt        = True
  (==) FKReal       FKReal       = True
  (==) FKIdentifier FKIdentifier = True
  (==) FKChar       FKChar       = True
  (==) FKString     FKString     = True
  (==) FKComment    FKComment    = True
  (==) FKOpenParen  FKOpenParen  = True
  (==) FKCloseParen FKCloseParen = True
  (==) _            _            = False


FsmToken : Type
FsmToken = Token FsmKind

comment : Lexer
comment = is ';' <+> is ';' <+> many (isNot '\n')

specialSymbol : Lexer
specialSymbol = oneOf "!$%&*/:<=>?^_~+-.@"

idnLit : Lexer
idnLit = (some (alphaNum <|> specialSymbol))

realLit : Lexer
realLit = opt (is '-') <+> digits <+> is '.' <+> digits

tokens : TokenMap FsmToken
tokens
  = toTokenMap [ (intLit,    FKInt)
               , (realLit,   FKReal)
               , (idnLit,    FKIdentifier)
               , (charLit,   FKChar)
               , (stringLit, FKString)
               , (is '(',    FKOpenParen)
               , (is ')',    FKCloseParen)
               , (spaces,    FKComment)
               , (comment,   FKComment)
               ]

public export
data SExp = IntAtom Int
          | RealAtom Double
          | SymbolAtom String
          | CharAtom Char
          | StringAtom String
          | SExpList (List SExp)

export
Show SExp where
  showPrec d (IntAtom n)    = showCon d "IntAtom" $ showArg n
  showPrec d (RealAtom n)   = showCon d "RealAtom" $ showArg n
  showPrec d (SymbolAtom s) = showCon d "SymbolAtom" $ showArg s
  showPrec d (CharAtom c)   = showCon d "CharAtom" $ showArg c
  showPrec d (StringAtom s) = showCon d "StringAtom" $ showArg s
  showPrec d (SExpList l)   = showCon d "SExpList" $ showArg l


Rule : Type -> Type
Rule ty = Grammar FsmToken True ty

int : Rule SExp
int = map IntAtom $ match FKInt

real : Rule SExp
real = map RealAtom $ match FKReal

identifier : Rule SExp
identifier = map SymbolAtom $ match FKIdentifier

char : Rule SExp
char = map CharAtom $ match FKChar

string : Rule SExp
string = map StringAtom $ match FKString

sexp : Rule SExp
sexp = int
   <|> real
   <|> identifier
   <|> char
   <|> string
   <|> do
       match FKOpenParen
       xs <- many sexp
       match FKCloseParen
       pure (SExpList xs)

export
parseSExp : String -> Either (ParseError FsmToken) (SExp, List FsmToken)
parseSExp inp
  = parse sexp (filter notComment (map TokenData.tok (fst (lex tokens inp))))
  where
    notComment : FsmToken -> Bool
    notComment t = case kind t of
                        FKComment => False
                        _ => True

export
parseErrorToString : ParseError a -> String
parseErrorToString (Error e _) = e
