%{
#include "parser.tab.h"
#include <string.h>
#include <stdlib.h>
%}

%%

"if"       { return IF; }
"else"     { return ELSE; }
"while"    { return WHILE; }
"for"      { return FOR; }
"sqrt"     { return SQRT; }
"pow"      { return POW; }
"log"      { return LOG; }
"exp"      { return EXP; }
"sin"      { return SIN; }
"cos"      { return COS; }
"tan"      { return TAN; }
"abs"      { return ABS; }

[0-9]+\.[0-9]+ { yylval.fv = atof(yytext); return FLOAT_NUM; }
[0-9]+         { yylval.iv = atoi(yytext); return INT_NUM; }

[a-zA-Z_][a-zA-Z0-9_]* { yylval.sv = strdup(yytext); return IDENTIFIER; }

"+"   { return PLUS; }
"-"   { return MINUS; }
"*"   { return MUL; }
"/"   { return DIV; }
"%"   { return MOD; }
"=="  { return EQ; }
"!="  { return NEQ; }
"<="  { return LE; }
">="  { return GE; }
"<"   { return LT; }
">"   { return GT; }
"&&"  { return AND; }
"||"  { return OR; }
"!"   { return NOT; }
"="   { return ASSIGN; }
"("   { return LPAREN; }
")"   { return RPAREN; }
"{"   { return LBRACE; }
"}"   { return RBRACE; }
";"   { return SEMICOLON; }
","   { return COMMA; }

[ \t\r\n]+  { }
"//".*      { }

.  { fprintf(stderr, "Unknown char: %s\n", yytext); }

%%

int yywrap(){ 
    return 1;
}
