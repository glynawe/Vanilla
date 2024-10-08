# Vanilla  [Draft]

Vanilla is a language in the Pascal family, the starting point of its design was Oberon. Vanilla has a module system with *functors*, a feature taken from OCaml. Functors are modules that take other modules as parameters. They are a single, simple mechanism that can provide features like abstract data types, generic types, traits, dependency injection and module extension.

[This version uses the original Oberon-like syntax.]

# Program Structure

## Definitions and Declarations

    Definition = VarDefinition | ProcDefinition | OtherDefinitions.

    DeclarationOrDefinition  = VarDeclaration | ProcDeclaration | OtherDefinitions.

    OtherDefinitions = Inclusion | ConstDefinition | TypeDefinition.

A *definition* names and describes a data type, procedure, variable, module or constant. A definition may be given more than once; definitions with the same name must have the same type.

A *declaration* is a definition that also defines *object code*. Object code is variable data or procedure code that will be included in an executable program. A declaration can only be made once.

## Modules and Interfaces

    Program = (Interface | Module| Functor) "."... ["."].

A Vanilla program may contain any number of interfaces, modules and functors separated by full stops. One module must declare a procedure called `main`, which will be the first procedure to be executed.

    Interface = "interface" InterfaceName "=" 
                {Definition ";"} 
                "end".

    Module    = "module" ModuleName [PublicInterface] "=" 
                {DeclarationOrDefinition ";"} 
                "end".

    Functor   = "module" ModuleName "(" ModuleParameter ";"... ")" 
                [PublicInterface] [TypeConstraints] "=" 
                {DeclarationOrDefinition ";"} 
                "end".

    PublicInterface  = ":" InterfaceName].
    ModuleParameter  = ModuleName ":" InterfaceName.
    TypeConstraints  = "where" TypeEquivalence ","... 
    TypeEquivalence  = TypeName ":=" ModuleName "_" TypeName.

    InterfaceName = NAME.
    ModuleName    = NAME.
    FunctorName   = NAME.
    TypeName      = NAME.

An *interface* contains a set of definitions. A *module* contains a set of definitions and declarations. The primary purpose of modules is group together collections of types and procedures to define abstract data types.

If a module is declared with a *public interface* then only the definitions in that interface will be available when the module is imported. The module must contain declarations for all the definitions in its public interface. 

 A *functor* is a module parametrized with a list of interfaces for modules that it can import; the actual modules are supplied when the functor is imported. The primary purpose of functors is to define generic abstract data types. Each module parameter has an interface that specifies a minimum set of definitions that the actual module must provide. A functor *type constraint* specifies types from different parameter modules that are to be equivalent (this is important when defining generic types). 

All interfaces and modules implicitly contain a set of *standard declarations* supplied by the Vanilla language. For example, the type `integer` is a standard declaration.

**Example**

    module Map (Key: Comparable; Value: ADT) where Map_KeyType := Key_Type, Map_ValueType := Value_Type =
        type MapType;
        type ValueType;
        type KeyType;
        procedure Set (map: MapType; key: KeyType; value: ValueType) = ... 
        ...
    end.

### Inclusion

    Inclusion     = Include | Import | FunctorImport.
    Include       = "include" ModuleName [TypeConstraints] ["for" NAME ","...].
    Import        = "import" ModuleName.
    FunctorImport = "import" ModuleName ":=" FunctorName "(" ModuleName ","... ")".

    ImportedName = ModuleName "_" NAME.
    GlobalName   = NAME | ImportedName. 

`include` includes content from other modules or interfaces. The contents of an interface are its definitions, the contents of a module are its declarations. If an `include` has a `for` clause then only a selection of its contents are included. A module can be included into another module with a set of type constraints, this allows the included module to add a set of *trait* procedures to those types. 

`import` includes content from other interfaces and modules, but each definition is given an *imported name*, which is the definition's name prefixed with the name of the interface. A *functor import* imports a new module created from a functor and a list of modules.

A module or interface's *global names* are the names of all its definitions.

A module without an explicit public interface has a default interface that excludes its imported names.

### Example

This very simplified program defines strings and generic sets as abstract data types. They are then used to create sets of strings. 

    interface COMPARABLE =
        type T;
        procedure Equal (a, b: T) : boolean;
    end.

    interface STRING =
        include COMPARABLE;
        type R;
        type T = ref R;
        procedure Create (text: array of byte): T;
    end.

    module String : STRING =
        type R = array of byte;
        procedure Equals (a, b: T) : boolean =
            return a = b or len(a) = len(b) and a^ = b^;
        end;
        procedure Create (text: array of byte): T =
            var s := new(byte, len(text)); s^ := text; return s;
        end;
    end.

    interface SET =
        type R;
        type T = ref R;
        type ET;
        val empty: T;
        procedure Add (set: T; element: ET) : T;
        procedure Includes (set: T; element: ET) : boolean;
    end.

    module Set (Element: COMPARABLE): SET where Set_ET := Element_T =
        type ET;
        type R = record value: Element; next: T end;
        val Empty: T := nil;
        procedure Add (set: T; element: ET) : T =
            var list := new(R); list.head := head; list.tail := tail;
            return list
        end;
        procedure Contains (set: T; element: ET) : boolean =
            while set != nil do
                if set.head.Equals(element) then return true
                else set := set.tail 
                end
            end;
            return false
        end;
    end.

    module Program =
        import Print;  
        import String;
        import StringSet := Set(String);
        procedure main () =
            val s := String_Create("Hello World!");
            var set := StringSet_Empty;
            set := set.Add(s);
            if set.Contains(s) then
                Print_String("Success!")
            end
        end; 
    end.

# Constants

    Constant = Expression.

    ConstDefinition = "const" NAME "=" Constant.

A Constant is an expression that is evaluated by the compiler. The declared length of an array is example of an expression that must be constant.  The only names allowed in a constant expression are the names of other constants and calls to standard procedures.

A ConstDefinition names a constant. A named constant may be described more than once, but the additional definitions must evaluate to the same value.


# Variables

    VarDefinition = ("var" | "val") VariableList.
    VarDeclaration = VarDefinition [":=" StructuredConstant].

    VariableList = NameList ":" Type.
    NameList     = NAME ","... .

A list of distinct variable definitions will be made if a list of names is given. `var a, b, c: t;` is shorthand for `var a: t; var b: t; var c: t;`

All of the variables named in the variable list of a VarDeclaration are initialized to the values in the VarDeclaration's structured constant. 

`val` declares a *immutable variable*, a variable that can only be assigned once when it is declared. *The compiler may arrange for immutable global variables to be stored in ROM.*

A variable definition has an implicit declaration if one is not given in a program's modules. E.g. the definition `var i: integer;` will be provided the declaration `var i: integer := 0;`.

## Structured Constants

A structured constant can be used to initialize global variables of any type, especially arrays and records. The value of a structured constant will become object code for the executable program.

    StructuredConstant = Constant | StructureList.
    StructureList      = "[" StructureItems ","... "]".
    StructureItems     = StructuredConstant ["for" Constant].

A structure list can be assigned to a record or array variable. Each item from a structure list is assigned to
an element of the record or array in order. For records that is that order used its definition. If those
elements are records or arrays then this rule is applied recursively.

A `for` clause indicates that an item should be repeated a number of times within its structure list.

A string literal can be used to declare a byte array. If it is shorter than the array then it is padded with zeros.

**Example** This array contains a one, three sevens and a six:

    var sevens: array 5 of integer := [1, 7 for 3, 6];

**Example** This array contains the bytes [64, 90, 64, 90, 0, 0, 0, 0]:

    val bytes: array 8 of byte := "AZAZ";


## Implicit Variable Declarations

A variable definition has an implicit declaration if one is not given in a program's modules. 

An implicit variable declaration has a default value. Numeric variables are initialized to zero. Reference variables are initialized to `nil`. The elements of arrays and records are recursively initialized by these rules. I.e. every non-structured value in a default structure ends up being zero or nil.

The above rule is also used to initialize local variables within procedure bodies.


# Types

    TypeDefinition = "type" NAME "=" Type | OpaqueType.
    OpaqueType     = "type" NAME.

    Type = GlobalName
         | "array" [DimensionList] "of" Type
         | "record" VariableList ";"... "end"
         | "ref" Type
         | "procedure" ProcType.

    DimensionList = Constant ","... .

Arrays begin at element 0. An array with more than one length in its dimension list describes an array of arrays. I.e. `array a, b, c of t` stands for `array a of array b of array c of t`. An array with no dimension list is an *open array*. An open array is one dimensional, and its length can be found using the standard procedure `len`. An open array type may only be used as the type of a parameter or as the target of a reference type.

A procedure type may only be used as the type of a parameter or as the target of a reference type.

An *opaque type* is a type whose definition is not yet given. An opaque type can be used in an interface to denote an abstract type or generic type parameter, or in a module to allow a record type to contain references to itself. An opaque type must be defined before it can be used in a module, either by a full type definition or a functor type constraint.

# Procedures

    ProcDefinition = "procedure" NAME ProcType.
    ProcDeclaration = ["loop"] ProcDefinition ["=" Body "end"].

    ProcType   = "(" [Parameters ";"...] ")" [ReturnType]
    Parameters = ["var"] VariableList.
    ReturnType = ":" Type

The parameter names in procedure definitions are placeholders for describing each parameter. They are not examined when determining type equivalence. However, parameters names are significant in procedure declarations.

A procedure with a return type is a *function procedure*. A procedure without a return type is a *proper procedure*. A function procedure may only be used in an expression. A proper procedure may only be used in a procedure call statement.

Assigning to a `var` parameter assigns to the parameter supplied by the procedure call, i.e. `var` parameters are passed by reference. Parameters without `var` are *value parameters*. Value parameters are immutable. *The compiler may pass record and array value parameters by reference.*

An array of any length may be passed to an *open array* parameter if their element types are the same. 

A procedure definition can be used in a module to define it early. This allows sets of mutually recursive procedures to be defined. (This like providing a *function prototype* in C or a *forward procedure* in Pascal.) 

A `loop` procedure must be tail-call optimizable. I.e. if the procedure calls itself recursively then that call must be optimizable into a loop. The compiler will reject the program if it cannot perform the optimisation. 

*A value parameter does not come with a guarantee that the parameter will retain the same value all though the execution of its procedure. "Aliasing" is possible. If a global variable is given as a parameter then assigning to that variable from within the procedure also changes the parameter's value.*

# Statements

    Body = Statement ";"... [";"].

    Statement = LocalDefinition
              | Assignment | ProcedureCall | If | Exit | Return | Case | Empty.

Statements appear in the bodies of procedures and within other statements.

## Local Declarations

    LocalDefinition = LocalVarDeclaration | ConstDefinition. 
    LocalVarDeclaration = ("var" | "val") NameList (":" Type [":=" Expression] | ":=" Expression).

Variables and constants defined in a statement body are only valid within that body, i.e. bodies are scopes. Variables and constants are only visible to the statements that come after their declaration statements. 

If a local variable declaration has an initializer expression then the expression is evaluated first and then all the variables named in its list are assigned that value, otherwise it is initialized to a default value by the same rules used to initialize global variables. If a local declaration has an initializer expression but no type then it takes on the type of its initializer. `val` declares a *immutable variable*, a variable that can only be assigned once when it is declared.  

A local definition may not have the same name as any definition in the same body or any surrounding body, including the procedure's parameter names. I.e. local names may not be shadowed. 

## Assignments

    Assignment = Designator ","... ":=" Expression

The expression is evaluated once then its value is assigned to each designator in the list. The designators are evaluated in order after the expression. The designators must have the same type as the expression.

Records of the same type and arrays of the same type and length may by assigned to each other.


## Procedure Calls

    ProcedureCall = Designator "(" [Expression ","...] ")"

The designator part of a procedure call statement must designate a proper procedure. 

The list of expressions in a procedure call are passed to the designated procedure as parameters. A `var` parameter must be passed a designator of the same type. A value parameter may be passed any expression, following the same rules as assignment.

### "Method calls"

If the start of a designator refers to a variable *v* of type *M_t*, and the last name in the designator refers to a procedure *M_p*, then `M_p(v, ...)` may be written as `v.p(...)`. (This is similar to the shorthand that Python uses for method calls.)

**Example**

If `list.head` has type `Set_t` and there is a procedure `Set_add(s: Set_t; v: vt)` then these two procedure calls mean the same thing:

```
Set_add(list.head, value)
list.head.add(value)
```

## If Statements

    If = "if" Expression "then" Body
         {"elsif" Expression "then" Body}
         ["else" Body]
         "end".

## Loop Statements

    Loop = ["loop" NAME]
           ["for" NAME ":=" Expression ["by" Constant] ("to" | "until") Expression]
           ["while" Expression]
           "do" Body
           "end".

A loop statement may be given a name to be used by `exit` statements.

Loop statements with no `for` or `while` clauses continue until a `return` statement or an applicable `exit` statement is executed.

If a loop statement has a `for` clause then its control variable name is an integer immutable variable in the statement's body. If there is a `while` clause then that variable may be used in that clause's expression. The limiting expressions of a `for` clause are evaluated only once.

If `to` is used in a `for` clause then the loop ends when the limiting expression is exceeded. If `until` is used in a `for` clause then the loop ends when the limiting expression is reached. `for i := 0 to 4 do print(i) end` would print `0 1 2 3 4` but `for i := 0 until 4 do print(i) end` would print `0 1 2 3`

**Example**

    procedure uppercase (var string: array of byte) =
        for i := 0 until len(string) while string[i] != '\0' do
            if string[i] >= 'A' and string[i] <= 'Z' then
                inc(string[i], 'A' - 'a')
            end
        end
    end;


## Exit Statements

    Exit = "exit" [NAME]

`exit` exits a loop statement. Either the loop that is named, or the innermost loop if no name is given. An exit statement can only appear inside a loop statement. A named exit statement can only appear inside a loop statement with the same name. 


## Return Statements

    Return = "return" [Expression].

`return` returns from a procedure immediately. If the procedure has a return type specified in its ProcDefinition then a return value must be supplied, and the procedure's execution must end with a return statement in every case.


## Case statements

    Case   = "case" Expression "of" {Branch} ["else" Body] "end".
    Branch = "|" Range ","... ":" Body.
    Range  = Constant [".." Constant].

Case expressions and range constants must be integers or bytes. All constants in a `case` statement must be unique and ranges must not overlap. If the expression's value is within a branch's ranges then that branch's Body is executed. If the value does not match a branch and there is an `else` clause then its body is executed; if there is no `else` clause then nothing is done.

*The highest range constant must be less than 256 higher that the lowest constant. Case statements are most useful when implemented using jump tables, and there must be some limit to the size of those tables.*

## Empty statement

    Empty = .

The main purpose of the empty statement is to allow superfluous semicolons in a body, e.g. after the final statement.

# Expressions

    Expression = Conjunction {"or" Conjunction}. 
    Conjunction = Relation {"and" Relation}.
    Relation = Sum [RelationOp Sum].
    Sum  = Term {AddOp Term}.
    Term = Factor {MulOp Factor}.

    AddOp  = "+" | "-".
    MulOp  = "*" | "/" | "mod".
    RelationOp = "=" | "!=" | ">" | "<" | ">=" | "<=".

    Factor = UnaryOp Factor
           | Designator
           | FunctionCall
           | Literal
           | Conditional
           | "(" Expression ")".

    FunctionCall = Designator "(" [Expression ","...] ")"

    UnaryOp = "+" | "-" | "not".

The list of expressions in a function call are supplied to the designated procedure as parameters. A `var` parameter must be supplied with a designator. A supplied parameter must match its parameter's type. 

## Operators

| Operators                 | Operand   | Operand   | Result    |
|---------------------------|-----------|-----------|-----------|
| `+` `-` `*` `/`           | *NumType* | *NumType* | *NumType* |
| `mod`                     | *IntType* | *IntType* | *IntType* |
| unary `-` `+`             | *NumType* |           | *NumType* |
| `=` `!=` `<` `<=` `>` `>=`| *NumType* | *NumType* | `boolean` |
| `=` `!=`                  | *RefType* | *RefType* | `boolean` |
| `and` `or`                | `boolean` | `boolean` | `boolean` |
| `not`                     | `boolean` |           | `boolean` |

*NumType* is `real`, `integer`, `word` or `byte`. *IntType* is `integer`, `word` or `byte`. *RefType* is any reference type. Operands and results must have the same type.

`x / y` and `x mod y` may raise an runtime error if *y* = 0. How that runtime error is handled is implementation-dependant behaviour.

Relational operators compare `integer`, `word`, `byte`, `real` and reference types. They return `boolean` values. References may only be compared for equality and inequality. Two references are equal if they refer to the same variable or both are `nil`.

### Logical operators

The `and` and `or` operators are "shortcut operators", they are equivalent to these conditional expressions:

`a or b`   ≡  `if a then true else b end`

`a and b`  ≡  `if a then b else false end`


## Conditional expressions

    Conditional  = "if" Expression "then" Expression
                   {"elsif" Expression "then" Expression}
                   "else" Expression
                   "end".

The expressions following `then` and `else` must have the same type.

## Designators, Procedure Calls

    Designator = GlobalName {Selection | Subscript | Dereference}.

    Selection   = "." NAME.
    Subscript   = "[" Expression ","... "]".
    Dereference = "^".

Reference values are automatically dereferenced when they are the designator of a call, selection or subscript.

## Literals

    Literal = INTEGER | REAL | CHARACTER | STRING.

INTEGER literals have the type `integer`. WORD literals has type `word`. BYTE literals have the type `byte`. REAL literals have the type `real`. STRING literals  are anonymous immutable variables of type `array of byte`. A string literal's array has an additional element at the end containing `'\0'`. 

BYTE, WORD and INTEGER literals are distinct. BYTE literals are either integer literals with the suffix `X` or character literals in single quotes. The range of BYTE literals is 0X to 255X. The range of WORD literals is 0 to `maxword`. WORD literals are integer literals with the suffix `L`. 

# Lexical Elements

## Numeric and String Literals 

    INTEGER  = DIGITS
             | "0x" HEXDIGIT {HEXDIGIT}
             | "0b" BINDIGIT {BINDIGIT}
             | "0o" OCTDIGIT {OCTDIGIT}.

    BYTE      = INTEGER "X" | CHARACTER.
    WORD      = INTEGER "L".
    CHARACTER = "'" (STRCHAR | '"' | "\'" | ESCAPE) "'".

    STRING    = '"' {STRCHAR | "'" | '\"' | ESCAPE} '"'.

    REAL     = DIGITS "." DIGITS [EXPONENT].

    EXPONENT = ("E" | "e") ["+" | "-"] DIGITS.
    DIGITS   = DIGIT {DIGIT}.
    DIGIT    = "0"..."9".
    BINDIGIT = "0" | "1".
    OCTDIGIT = "0"..."7".
    HEXDIGIT = "0"..."9" | "A"..."F".
    ESCAPE    = "\a" | "\b" | "\e" | "\f" | "\n" | "\t" | "\v" | "\0" | "\\" |
                "\x" HEXDIGIT HEXDIGIT.
    STRCHAR   = " "..."~" except for "\", "'" and '"'.

## Names

    NAME    = LETTER {LETTER | DIGIT}.
    LETTER  = "A"..."Z" | "a"..."z".
    DIGIT   = "0"..."9".

    ImportedName = ModuleName "_" NAME.
    ModuleName   = NAME.

The underscore is reserved for prefixing imported names with module names.

## Keywords

    Keywords = 
        "and" | "array" | "by" | "case" | "const" | "do" | "else" | "elsif" |
        "end" | "exit" | "for" | "if" | "import" | "include" | "interface" | "loop" |
        "mod" | "module" | "not" | "of" | "or" | "procedure" |  "record" |
        "ref" | "return" | "then" | "to" | "type" | "until" | "val" | "var" | where" | 
        "while".

    StandardDefinitionNames =
        "abs" | "assert" | "boolean" | "byte" | "dec" | "halt" | "expect" |
        "false" | "free" | "inc" | "integer" | "land" | "len" | 
        "lenint" | "lnot" | "lor" |  "lxor" | "main" | "maxint" | "maxword" | "minint" |
        "new" | "nil" | "real" | "sha" | "shl" | "shr" | "true" | "word" | "SYSTEM" |
        "ADDRESS" | "GET" | "MOVE" | "PUT" | "REF" | "SIZE" | "TYPE" | "TYPESIZE".

Keywords and the names of standard declarations may not be used for any other purpose. 

## Whitespace and comments

    WHITESPACE = SPACER {SPACER}.
    SPACER     = COMMENT | " " | CR | LF | TAB.
    COMMENT    = "//" {" "..."~" | TAB} (CR | LF).

Adjacent names and keywords must be separated by whitespace. Whitespace is allowed anywhere except inside lexical elements (syntactic elements between double quotes and elements with all-uppercase names). Comments begin with `//` and end at the end of the line. Comments are allowed anywhere that whitespace is allowed.

## Source files

    SourceFile = (Interface | Module) {Interface | Module}.

A Vanilla source file contains one or more interfaces or modules. The names of the files are not significant, but the file extension `.van` should be used by convention.


# The standard declarations

The standard declarations are implicitly included at the start of every interface and module. Their names cannot be used for other purposes.

## Standard Types

| Name      | Contents                                                   |
|-----------|------------------------------------------------------------|
| `boolean` | The logical values `true` or `false`.                      |
| `integer` | Two's-complement signed integers.                          |
| `word`    | Unsigned integers between 0 and `maxword`.                 |
| `byte`    | Integers between 0 and 255. Also used to store characters. |
| `real`    | Floating-point numbers.                                    |

The floating-point number representation is implementation-dependant. `integer` should have a convenient range for arithmetic. `word` must be wide enough to contain a memory address.


## Standard Constants

| Name     | Value                                                             |
|----------|-------------------------------------------------------------------|
| `minint` | the lowest possible integer value                                 |
| `maxint` | the highest possible integer value                                |
| `maxword`| the highest possible word value                                   |
| `lenint` | the number of bits required to store an integer                   |
| `lenword`| the number of bits required to store a word                       |
| `nil`    | is the value of ref variables that are not pointing to variables. |
| `true`   |                                                                   |
| `false`  |                                                                   |

The constant `nil` may be assigned to any reference variable. A variable containing `nil` must not be dereferenced.

The values of `minint`, `maxint` and `lenint` are implementation-dependant.

## Standard Procedures

The standard procedures are operators that resemble procedure calls. Some are polymorphic, some take type definitions as parameters. Standard procedures may be used within constant expressions. 

In the following tables *IntType* is an `integer`, `word` or `byte` value, *NumType* is an integer type or `real`, `T` is a name of a type and *Array* is any array variable.

| Definition                            | Function                             |
|---------------------------------------|--------------------------------------|
| `abs (x: integer) : integer`          | absolute value of `x`                |
| `abs (x: real) : real`                | absolute value of `x`                |
| `dec (var v: IntType)`                | `v := v - 1`                         |
| `dec (var v: IntType; n: IntType)`    | `v := v - n`                         |
| `inc (var v: IntType)`                | `v := v + 1`                         |
| `inc (var v: IntType; n: IntType)`    | `v := v + n`                         |
| `len (a: Array; n: IntConst)`         | length of dimension `n` of array `a` |
| `len (a: Array)`                      | equivalent to `len(v, 0)`            |
| `as (v: NumType; T): NumType`         | convert `v` to numeric type `T`.     |
| `fits (T; v: NumType): boolean`       | true if `v` will fit in type `T`.    |


`inc` and `dec` evaluate their variable parameters only once.

`len(a, 0)` is the length of the first dimension of array `a`.

`as` may raise an runtime error if its parameter value are outside its return type's range. `fits` can be used to determine if that will happen. How runtime errors are handled is implementation-dependant behaviour.

### Bit Manipulation Procedures

| Definition                                | Function                                  |
|-------------------------------------------|-------------------------------------------|
| `lnot (x: IntType) : IntType`             | bitwise logical NOT                       |
| `land (x, y: IntType) : IntType`          | bitwise logical AND                       |
| `lor (x, y: IntType) : IntType`           | bitwise logical inclusive-OR              |
| `lxor (x, y: IntType) : IntType`          | bitwise logical exclusive-OR              |
| `shl (x: IntType; n: integer) : IntType`  | left-shift bits of `x` by `n`             |
| `shr (x: IntType; n: integer) : IntType`  | right-shift bits of `x` by `n`            |
| `sha (x: IntType; n: integer) : IntType`  | arithmetic right-shift bits of `x` by `n` |

The bit shift operators will shift in the opposite direction if *n* is negative. Shifting by more than the width of *x* results in 0, or -1 in the case of an arithmetic right-shift. 

### Memory allocation procedures

| Definition                             | Function                          |
|----------------------------------------|-----------------------------------|
| `new (T) : ref T`                      | allocate data                     |
| `new (T; d: integer) : ref array of T` | allocate an array of `d` elements |
| `free (r : ref T)`                     | free data                         |

`new` and `free` may not be used in constant expressions. The type `T` may not be an opaque type or open array (its size must be known).

#### Garbage Collection Option

The `new` procedure takes a type definition as its first parameter, finds memory space for an anonymous variable of that type, assigns a default initial value to the variable and returns a reference to it. If no memory space is available then a runtime error is raised. 

The `free` procedure does nothing. 

#### Manual Allocation Option

`new` and `free` exist to provide a type safe way to use low-level `ALLOCATE` and `DEALLOCATE` procedures. `ALLOCATE` and `DEALLOCATE` procedure definitions must be included in any module that calls `new` or `free`. How the procedures are implemented is up to the programmer. They will typically be included from the interface of a module that manages memory on a heap. 

    procedure ALLOCATE (size: integer): word;  // returns an address
    procedure DEALLOCATE (address: word);

The `new` procedure calls `ALLOCATE(SYSTEM_TYPESIZE(T))` or `ALLOCATE(SYSTEM_TYPESIZE(T) * d)` to obtain the address of memory space for an anonymous variable of  type `T`. If that address is 0 then an runtime error is raised, otherwise the anonymous variable is assigned a default initial value and a reference to it is returned.

The `free(r)` procedure calls `DEALLOCATE(SYSTEM_TYPE(r, integer))` to mark the space at *r* as free for reallocation.

### Halting procedures

| Definition            | Function                          |
|-----------------------|-----------------------------------|
| `halt (n: integer)`   | halt with exit code *n*           |
| `assert (x: boolean)` | raise runtime error if not *x*    |
| `expect (x: boolean)` | raise runtime error if not *x*    |

 `assert` is for testing if the program is correct. `expect` is for testing whether the program should continue, e.g. testing whether an operating system service is still functioning. *The execution of `assert` may optionally be turned off by the compiler.*

How runtime errors and exit codes are handled is implementation-dependant behaviour.

**Example**

    assert(String_length(text) > 0);    // The program created text.
    status := Cstdio_fputs(text, file);
    expect(status != Cstdio_EOF);       // The I/O system is working.
    halt(0);                            // The program is finished now.


# The SYSTEM Interface

Including the interface `SYSTEM` allows a set of "unsafe" standard procedures to be used. Unsafe procedures access computer hardware or circumvent the type system. A module that includes `SYSTEM` should be considered unsafe. An unsafe module may have a safe interface.

If a particular computer requires language extensions, e.g. procedures that access CPU registers, then they should be added to `SYSTEM`.

In the following table *RAM* refers the computer's random access memory, addressed by byte; *AnyType* is any type; *T* is a type definition given as a parameter.

|  Definition                         | Function                                     |
|--------------------------------------|----------------------------------------------|
| `ADDRESS (var v: AnyType) : word`    | address of variable `v`                      |
| `MOVE (a, b, n: integer)`            | move `n` bytes from `RAM[a]` to `RAM[b]`     |
| `GET (a: word; var v: AnyType)`      | fill `v` with the bytes starting at `RAM[a]` |
| `PUT (a: word; v: AnyType)`          | move the bytes of `v` to `RAM[a]`            |
| `SIZE (v : AnyType) : integer`       | number of bytes in variable `v`              |
| `REF (var v: AnyType) : ref AnyType` | make a reference to a variable or procedure  |
| `TYPESIZE (T)  : word`               | number of bytes required by type `T`         |
| `TYPE (x: AnyType; T) : T`           | give `x` the type `T`                        |

`TYPE` changes the type of a value or variable without altering the underlying bits that represent it. E.g. it can be used to represent a reference as an word or a record as an array of bytes.

**Example**

    interface IntegerRepresentation =
        procedure EndianReversal (x: integer) : integer;
    end.

    module IntegerRepresentation =
        include SYSTEM;
        procedure EndianReversal (x: integer) : integer =
            const w = SIZE(x);
            val a := TYPE(x, array w of byte);
            var b: array w of byte;
            for i := 0 until w do
                b[i] := a[w - i - 1]
            end;
            return TYPE(b, integer)
        end;
    end.
