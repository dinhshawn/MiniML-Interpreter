/*
                         CS 51 Final Project
                           MiniML -- Parser
*/

%{
  open Printf ;;
  open Expr ;;
%}

%token EOF
%token OPEN CLOSE
%token LET DOT IN REC
%token NEG
%token PLUS MINUS FPLUS FMINUS
%token TIMES FTIMES
%token LESSTHAN EQUALS
%token IF THEN ELSE
%token FUNCTION
%token RAISE
%token UNIT
%token <string> ID
%token <char> CHAR
%token <string> STR
%token <int> INT
%token <float> FLOAT
%token TRUE FALSE

%nonassoc LESSTHAN
%nonassoc EQUALS
%left PLUS MINUS FPLUS FMINUS
%left TIMES FTIMES
%left NEG

%start input
%type <Expr.expr> input

/* Grammar follows */
%%
input:  exp EOF                 { $1 }

exp:    exp expnoapp            { App($1, $2) }
        | expnoapp              { $1 }

expnoapp: INT                   { Num $1 }
        | FLOAT                 { Float $1 }
        | TRUE                  { Bool true }
        | FALSE                 { Bool false }
        | CHAR                  { Char $1 }
        | STR                   { Str $1 }
        | ID                    { Var $1 }
        | exp PLUS exp          { Binop(Plus, $1, $3) }
        | exp MINUS exp         { Binop(Minus, $1, $3) }
        | exp TIMES exp         { Binop(Times, $1, $3) }
        | exp FPLUS exp         { Binop(Fplus, $1, $3) }
        | exp FMINUS exp        { Binop(Fminus, $1, $3) }
        | exp FTIMES exp        { Binop(Ftimes, $1, $3) }
        | exp EQUALS exp        { Binop(Equals, $1, $3) }
        | exp LESSTHAN exp      { Binop(LessThan, $1, $3) }
        | NEG exp               { Unop(Negate, $2) }
        | IF exp THEN exp ELSE exp      { Conditional($2, $4, $6) }
        | LET ID EQUALS exp IN exp      { Let($2, $4, $6) }
        | LET REC ID EQUALS exp IN exp  { Letrec($3, $5, $7) }
        | FUNCTION ID DOT exp   { Fun($2, $4) }
        | RAISE                 { Raise }
        | UNIT                  { Unit }
        | OPEN exp CLOSE        { $2 }
;

%%
