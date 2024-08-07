(* ---------------------------------------------------------------------------
MARK: Literals 
*)

%token <unit> NAME
%token <unit> INTEGER_LITERAL
%token <unit> BYTE_LITERAL
%token <unit> CHAR_LITERAL
%token <unit> WORD_LITERAL
%token <unit> STRING_LITERAL
%token <unit> FLOAT_LITERAL
%token EOF


(* ---------------------------------------------------------------------------
MARK: Operators 
*)

%token ADD "+"  
%token AND "&&"
%token ASSIGN "="
%token ASSIGN_ADD "+="
%token ASSIGN_SUB "-="
%token CARET "^"
%token CONTAINS "::"
%token DEC "--"
%token DIV "/"   
%token EQ "=="  
%token GE ">="
%token GT ">"  
%token INC "++"
%token LE "<="  
%token LT "<"  
%token MOD "%"  
%token MUL "*"  
%token NE "!="  
%token NOT "!"
%token OR "||"
%token SUB "-"  
%token QUESTION "?"

%left "||"
%left "&&"
%nonassoc  "<" "<=" "==" "!=" ">" ">="
%left "+"  "-"
%left "*" "/" "%"
%left "!"  (* also unary "-" and "+" *)


(* ---------------------------------------------------------------------------
MARK: Punctuation 
*)

%token BRA "("
%token KET ")"
%token COMMA ","
%token FULLSTOP "."
%token RANGE ".."
%token COLON ":"
%token SEMICOLON ";"
%token SBRA "["
%token SKET "]"
%token CBRA "{"
%token CKET "}"


(* ---------------------------------------------------------------------------
MARK: Keywords 
*)

%token BOOL "bool"
%token BREAK "break"
%token BYTE "byte"
%token CASE "case"
%token CONST "const"
%token DEFAULT "default"
%token ELSE "else"
%token FALSE "false"
%token FLOAT "float"
%token FN "fn"
%token FOR "for"
%token IF "if"
%token INT "int"
%token IMPORT "import"
%token INCLUDE "include"
%token INTERFACE "interface"
%token LET "let"
%token LOOP "loop"
%token MODULE "module"
%token NEW "new"
%token NIL "nil"
%token REF "ref"
%token RETURN "return"
%token STRUCT "struct"
%token SWITCH "switch"
%token TRUE "true"
%token TYPE "type"
%token TYPEFN "TYPE"
%token TYPESIZE "TYPESIZE"
%token VAR "var"
%token WHERE "where"
%token WHILE "while"
%token WORD "word"

(* ---------------------------------------------------------------------------
MARK: Rule Types 
*)

%type <unit> block
%type <unit> case
%type <unit> closed_statement
%type <unit> declaration
%type <unit> default
%type <unit> definition
%type <unit> designator
%type <unit> elements 
%type <unit> expr
%type <unit> expression
%type <unit> functioncall
%type <unit> globalname
%type <unit> importedname
%type <unit> limiter
%type <unit> moduledecl
%type <unit> moduleparameter
%type <unit> name
%type <unit> open_statement
%type <unit> otherdefinitions
%type <unit> parameters
%type <unit> proctype
%type <unit> program
%type <unit> publicinterface
%type <unit> range
%type <unit> repetition
%type <unit> selection
%type <unit> simple_statement
%type <unit> statement
%type <unit> structure
%type <unit> structuredconstant
%type <unit> structureitems
%type <unit> typeconstraint
%type <unit> typeconstraints
%type <unit> typedef
%type <unit> typesuffix
%type <unit> varlist


%start program

%%

%inline commas(X) : xs=separated_nonempty_list(",", X)
    { () }


/* ---------------------------------------------------------------------------
MARK: Modules 
*/

program : moduledecl+ EOF
    { () }

moduledecl : 
| "interface" n=NAME "{" ds=definition* "}"
    { () }
| "module" n=NAME i=publicinterface? "{" ds=declaration* "}"
    { () }
| "module" n=NAME "<" ps=commas(moduleparameter) ">"
  i=publicinterface? c=loption(typeconstraints) "{" ds=declaration* "}"
    { () }

moduleparameter 
: n1=name ":" n2=name
    { () }

publicinterface 
: ":" n=name
    { () }

typeconstraints 
: "where" tc=commas(typeconstraint)
    { () }

typeconstraint : n1=NAME "=" n2=importedname
    { () }


/* ---------------------------------------------------------------------------
MARK: Declarations 
*/

definition : 
| "var" ns=commas(name) t=typesuffix ";"
    { () }  
| "let" commas(name) typesuffix ";"
    { () }  
| "fn" n=NAME pt=proctype ";"
    { () }  
| "import" n=NAME ";"
    { () }  
| "import" n1=NAME "=" n2=NAME "<" ns=commas(name) ">" ";"
    { () }  
| "include" n=NAME tc=typeconstraints? ns=selection? ";"
    { () }  
| d=otherdefinitions 
    { () }

declaration: 
| "var" ns=commas(name) t=typesuffix sc=structuredconstant? ";"
    { () }  
| "let" commas(name) typesuffix structuredconstant ";"
    { () }  
| l=boption("loop") "fn" n=NAME pt=proctype b=block
    { () }  
| "import" n=NAME ";"
    { () }  
| "import" n1=NAME "=" n2=NAME "<" ns=commas(name) ">" ";"
    { () }  
| "include" n=NAME tc=typeconstraints? ns=selection? ";"
    { () }  
| d=otherdefinitions 
    { () }

otherdefinitions : 
| "const" NAME "=" e=expression ";"
    { () }  
| "type" n=NAME "=" t=typedef ";"
    { () }  
| "type" NAME ";"
    { Defn_AbsType n @ $loc($1) }  

selection 
: "for" ns=commas(name)
    { () }

varlist 
: ns=commas(name) t=typesuffix
    { () }

structuredconstant 
: expression
    { () }
| sc=structure
    { () }

structure 
: "{" ss=commas(structureitems) "}"
    { () }

structureitems 
: sc=structuredconstant r=repetition?
    { () }

repetition 
: "for" e=expression
    { () }


/* --------------------------------------------------------------------------- 
MARK: Types 
*/

typedef
: n=globalname
    { () }
| "[" e=expression "]" t=typedef
    { () }
| "[" "]" t=typedef
    { () }
| "struct" "{" es=elements* "}"
    { () }
| "ref" t=typedef
    { () }
| "byte"
    { () }
| "int"
    { () }
| "word"
    { () }
| "float"
    { () }
| "bool"
    { () }
| "fn" pt=proctype
    { () }

proctype
: l="(" ps=separated_list(",", parameters) ")" t=typesuffix?
    { () }

parameters
: "var" varlist
    { () }
| varlist
    { () }

elements
: vs=varlist ";"
    { () }

typesuffix : ":" t=typedef
    { () }


/* ---------------------------------------------------------------------------
MARK: Statements 
*/

block
: "{" statement* "}" 
    { () }

statement
: s=open_statement { s }
| s=closed_statement { s }

open_statement
: "if" "(" e=expression ")" s1=statement  
    { () }
| "if" "(" e=expression ")" s1=closed_statement "else" s2=open_statement  
    { () }
| "for" n1=name? "(" n2=NAME "=" e1=expression limiter expression ")" s=open_statement  
    { () }
| "while" n1=name? "(" e=expression ")" s=open_statement  
    { () }

closed_statement
: s=simple_statement 
    { s }
| "if" "(" e=expression ")" s1=closed_statement "else" s2=closed_statement  
    { () }
| "for" n1=name? "(" n2=NAME "=" e1=expression limiter expression ")" s=closed_statement  
    { () }
| "while" n1=name? "(" e=expression ")" s=closed_statement  
    { () }

simple_statement
: block
    { () }
| "var" ns=commas(name) t=typesuffix ";"   
    { () }
| "var" ns=commas(name) t=typesuffix "=" e=expression ";"   
    { () }
| "var" commas(name) "=" e=expression ";"  
    { () }
| "let" commas(name) typesuffix "=" expression ";"  
    { () }
| "let" commas(name) "=" expression ";"  
    { () }
| "break" n=name? ";"  
    { () }
| "switch" "(" e=expression ")" "{" cs=case* d=default? "}"
    { () }
| f=functioncall ";"
    { () }
| d=designator "=" e=expression ";"
    { () }
| d=designator "+=" e=expression ";"
    { () }
| d=designator "-=" e=expression ";"
    { () }
| "++" d=designator ";"
    { () }
| "--" d=designator ";"
    { () }
| "loop" n=name? block  
    { () }
| "return" e=expression? ";"
    { () }
| ";"
    { () }

limiter
: ".."  { () }
| ":"   { () }

case 
: "case" separated_nonempty_list(",", range) ":" ss=statement+
    { () }

range 
: e=expression
    { () }
| e1=expression ".." e2=expression
    { () }

default 
: "default" ":" ss=statement+
    { () }



/* ---------------------------------------------------------------------------
MARK: Expressions 
*/

expression
: e=expr
    { () }
| e1=expr "?" e2=expr ":" e3=expression
    { () }

expr
: "(" e=expression ")"
    { () }
| x=INTEGER_LITERAL
    { () }
| x=BYTE_LITERAL
    { () }
| x=FLOAT_LITERAL
    { () }
| x=CHAR_LITERAL
    { () }
| x=WORD_LITERAL
    { () }
| x=STRING_LITERAL
    { () }
| "true"
    { () }
| "false"
    { () }
| "nil"
    { () }
| d=designator
    { () }
| f=functioncall
    { () }
| "!" e=expr
    { () }
| "+" e=expr  %prec NOT
    { () }
| "-" e=expr  %prec NOT
    { () }
| e1=expr "||" e2=expr
    { () }
| e1=expr "&&" e2=expr
    { () }
| e1=expr "==" e2=expr
    { () }
| e1=expr "!=" e2=expr
    { () }
| e1=expr "<"  e2=expr
    { () }
| e1=expr "<=" e2=expr
    { () }
| e1=expr ">"  e2=expr
    { () }
| e1=expr ">=" e2=expr
    { () }
| e1=expr "+"  e2=expr
    { () }
| e1=expr "-"  e2=expr
    { () }
| e1=expr "*"  e2=expr
    { () }
| e1=expr "/"  e2=expr
    { () }
| e1=expr "%"  e2=expr
    { () }
| "new" "(" t=typedef ")"
    { () }
| "new" "(" t=typedef "," e=expression ")"
    { () }
| "TYPESIZE" "(" t=typedef ")"
    { () }
| "TYPE" "(" e=expression "," t=typedef ")"
    { () }

functioncall 
: d=designator "(" es=separated_list(",", expression) ")"  
    { () }


/* ---------------------------------------------------------------------------
MARK: Designators 
*/

designator
: n=globalname
    { () }
| d=designator "." n=NAME
    { () }
| d=designator "^"
    { () }
| d=designator "[" e=expression "]"
    { () }

name 
: n=NAME
    { () } 

globalname 
: n=name
    { () } 
| n=importedname
    { () } 

importedname 
: n1=name "::" n2=name
    { () }

