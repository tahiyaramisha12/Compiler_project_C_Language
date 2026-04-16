%{
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>

void yyerror(const char *s);
int yylex(void);

FILE *tac_file;
FILE *asm_file;

static int tc=0, lc=0, rc=0;

char *nt(){ char *b=malloc(16); sprintf(b,"t%d",++tc); return b; }
char *nl(){ char *b=malloc(16); sprintf(b,"L%d",++lc); return b; }
char *nr(){ char *b=malloc(8);  sprintf(b,"R%d",rc++%8); return b; }

void et(const char *f,...){ va_list a; va_start(a,f); vfprintf(tac_file,f,a); va_end(a); fprintf(tac_file,"\n"); }
void ea(const char *f,...){ va_list a; va_start(a,f); vfprintf(asm_file,f,a); va_end(a); fprintf(asm_file,"\n"); }

static char *stk[256]; static int top=0;
void  psh(const char *s){ stk[top++]=strdup(s); }
char *pop(){ return top>0?stk[--top]:strdup("ERR"); }

int isn(const char *s){ return s&&(s[0]=='-'||(s[0]>='0'&&s[0]<='9')); }

void mv(const char *r,const char *v){
    if(isn(v)) ea("  MOV %s, #%s",r,v);
    else       ea("  MOV %s, %s",r,v);
}

const char *opc(const char *o){
    if(!strcmp(o,"+"))  return "ADD";
    if(!strcmp(o,"-"))  return "SUB";
    if(!strcmp(o,"*"))  return "MUL";
    if(!strcmp(o,"/"))  return "DIV";
    if(!strcmp(o,"%"))  return "MOD";
    if(!strcmp(o,">"))  return "CMP_GT";
    if(!strcmp(o,"<"))  return "CMP_LT";
    if(!strcmp(o,">=")) return "CMP_GE";
    if(!strcmp(o,"<=")) return "CMP_LE";
    if(!strcmp(o,"==")) return "CMP_EQ";
    if(!strcmp(o,"!=")) return "CMP_NE";
    if(!strcmp(o,"&&")) return "AND";
    if(!strcmp(o,"||")) return "OR";
    return "NOP";
}

char *bop(const char *l,const char *op,const char *r){
    char *t=nt(),*r1=nr(),*r2=nr(),*rd=nr();
    et("%s = %s %s %s",t,l,op,r);
    mv(r1,l); mv(r2,r);
    ea("  %s %s, %s, %s",opc(op),rd,r1,r2);
    ea("  MOV %s, %s",t,rd);
    free(r1); free(r2); free(rd);
    return t;
}

void asgn(const char *v,const char *val){
    char *r=nr();
    et("%s = %s",v,val);
    mv(r,val);
    ea("  MOV %s, %s",v,r);
    free(r);
}

char *fn1(const char *fn,const char *a){
    char *t=nt(),*r=nr();
    char up[16]; int i;
    for(i=0;fn[i]&&i<15;i++) up[i]=(fn[i]>='a'&&fn[i]<='z')?fn[i]-32:fn[i];
    up[i]=0;
    et("%s = %s(%s)",t,fn,a);
    mv(r,a);
    ea("  %s %s",up,r);
    ea("  MOV %s, %s",t,r);
    free(r); return t;
}

char *fn2(const char *fn,const char *a,const char *b){
    char *t=nt(),*r1=nr(),*r2=nr();
    et("%s = %s(%s, %s)",t,fn,a,b);
    mv(r1,a); mv(r2,b);
    ea("  POW %s, %s",r1,r2);
    ea("  MOV %s, %s",t,r1);
    free(r1); free(r2); return t;
}
%}

%union { int iv; float fv; char *sv; }

%token IF ELSE WHILE FOR
%token SQRT POW LOG EXP SIN COS TAN ABS
%token PLUS MINUS MUL DIV MOD
%token EQ NEQ LT GT LE GE AND OR NOT
%token ASSIGN LPAREN RPAREN LBRACE RBRACE SEMICOLON COMMA
%token <iv> INT_NUM
%token <fv> FLOAT_NUM
%token <sv> IDENTIFIER

%type <sv> expr term factor unary rel lg

%right ASSIGN
%left OR
%left AND
%left EQ NEQ
%left LT GT LE GE
%left PLUS MINUS
%left MUL DIV MOD
%right NOT UMINUS

%%

prog : stmts ;

stmts : stmts stmt | stmt ;

stmt
    : IDENTIFIER ASSIGN expr SEMICOLON { asgn($1,$3); free($1); free($3); }
    | IDENTIFIER ASSIGN expr           { asgn($1,$3); free($1); free($3); }
    | ifst
    | whilest
    | forst
    ;

blk : LBRACE stmts RBRACE | LBRACE RBRACE ;

ep
    : ELSE blk { char *l=pop(); et("%s:",l); ea("%s:",l); free(l); }
    |          { char *l=pop(); et("%s:",l); ea("%s:",l); free(l); }
    ;

ifst
    : IF LPAREN lg RPAREN
        {
            char *l=nl();
            et("ifFalse %s goto %s",$3,l);
            ea("  CMP %s, #0",$3);
            ea("  JE %s",l);
            psh(l); free($3); free(l);
        }
      blk
        {
            char *e=nl();
            et("goto %s",e);
            ea("  JMP %s",e);
            char *l=pop();
            et("%s:",l); ea("%s:",l);
            psh(e); free(l);
        }
      ep
    ;

whilest
    : WHILE LPAREN
        {
            char *l=nl();
            et("%s:",l); ea("%s:",l);
            psh(l); free(l);
        }
      lg RPAREN
        {
            char *e=nl();
            et("ifFalse %s goto %s",$4,e);
            ea("  CMP %s, #0",$4);
            ea("  JE %s",e);
            psh(e); free($4); free(e);
        }
      blk
        {
            char *e=pop();
            char *l=pop();
            et("goto %s",l); ea("  JMP %s",l);
            et("%s:",e);     ea("%s:",e);
            free(e); free(l);
        }
    ;

forst
    : FOR LPAREN IDENTIFIER ASSIGN expr SEMICOLON
        {
            asgn($3,$5);
            char *l=nl();
            et("%s:",l); ea("%s:",l);
            psh(l); psh($3);
            free($5); free(l);
        }
      lg SEMICOLON
        {
            char *e=nl();
            et("ifFalse %s goto %s",$8,e);
            ea("  CMP %s, #0",$8);
            ea("  JE %s",e);
            psh(e); free($8); free(e);
        }
      IDENTIFIER ASSIGN expr RPAREN blk
        {
            char *ie=strdup($13);
            char *iv=strdup($11);
            char *e=pop();
            char *lv=pop();
            char *ls=pop();
            free($11); free($13);
            asgn(iv,ie);
            et("goto %s",ls); ea("  JMP %s",ls);
            et("%s:",e);      ea("%s:",e);
            free(ie); free(iv); free(e); free(lv); free(ls);
        }
    ;

lg
    : lg AND rel { $$=bop($1,"&&",$3); free($1); free($3); }
    | lg OR  rel { $$=bop($1,"||",$3); free($1); free($3); }
    | NOT rel
        {
            char *t=nt(); char *r=nr();
            et("%s = !%s",t,$2);
            ea("  MOV %s, %s",r,$2);
            ea("  NOT %s",r);
            ea("  MOV %s, %s",t,r);
            free(r); free($2); $$=t;
        }
    | rel { $$=$1; }
    ;

rel
    : expr GT  expr { $$=bop($1,">" ,$3); free($1); free($3); }
    | expr LT  expr { $$=bop($1,"<" ,$3); free($1); free($3); }
    | expr GE  expr { $$=bop($1,">=",$3); free($1); free($3); }
    | expr LE  expr { $$=bop($1,"<=",$3); free($1); free($3); }
    | expr EQ  expr { $$=bop($1,"==",$3); free($1); free($3); }
    | expr NEQ expr { $$=bop($1,"!=",$3); free($1); free($3); }
    | expr          { $$=$1; }
    ;

expr
    : expr PLUS  term { $$=bop($1,"+",$3); free($1); free($3); }
    | expr MINUS term { $$=bop($1,"-",$3); free($1); free($3); }
    | term            { $$=$1; }
    ;

term
    : term MUL factor { $$=bop($1,"*",$3); free($1); free($3); }
    | term DIV factor { $$=bop($1,"/",$3); free($1); free($3); }
    | term MOD factor { $$=bop($1,"%",$3); free($1); free($3); }
    | factor          { $$=$1; }
    ;

factor
    : unary                              { $$=$1; }
    | LPAREN lg RPAREN                   { $$=$2; }
    | SQRT LPAREN expr RPAREN            { $$=fn1("sqrt",$3); free($3); }
    | LOG  LPAREN expr RPAREN            { $$=fn1("log" ,$3); free($3); }
    | EXP  LPAREN expr RPAREN            { $$=fn1("exp" ,$3); free($3); }
    | SIN  LPAREN expr RPAREN            { $$=fn1("sin" ,$3); free($3); }
    | COS  LPAREN expr RPAREN            { $$=fn1("cos" ,$3); free($3); }
    | TAN  LPAREN expr RPAREN            { $$=fn1("tan" ,$3); free($3); }
    | ABS  LPAREN expr RPAREN            { $$=fn1("abs" ,$3); free($3); }
    | POW  LPAREN expr COMMA expr RPAREN { $$=fn2("pow",$3,$5); free($3); free($5); }
    ;

unary
    : MINUS factor %prec UMINUS
        {
            char *t=nt(); char *r=nr();
            et("%s = -%s",t,$2);
            ea("  MOV %s, %s",r,$2);
            ea("  NEG %s",r);
            ea("  MOV %s, %s",t,r);
            free(r); free($2); $$=t;
        }
    | INT_NUM   { char *b=malloc(32); sprintf(b,"%d",$1);   $$=b; }
    | FLOAT_NUM { char *b=malloc(32); sprintf(b,"%.6g",$1); $$=b; }
    | IDENTIFIER { $$=$1; }
    ;

%%

void yyerror(const char *s){ fprintf(stderr,"Error: %s\n",s); }

int main(int argc,char *argv[]){
    extern FILE *yyin;
    if(argc>1){ yyin=fopen(argv[1],"r"); if(!yyin){perror(argv[1]);return 1;} }
    tac_file=fopen("tac.txt","w");
    asm_file=fopen("assembly.txt","w");
    fprintf(tac_file,"");
    fprintf(asm_file,"");
    yyparse();
    fclose(tac_file); fclose(asm_file);
    if(argc>1) fclose(yyin);
    printf("Done. tac.txt + assembly.txt written.\n");
    return 0;
}