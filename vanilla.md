# Vanilla  [Draft]

Vanilla is a language in the Pascal family, the starting point of its design was Oberon.

I have taken a non-Oberon-like approach to describing declarations and modules. I will later extend the module system with [functors](https://v2.ocaml.org/manual/moduleexamples.html#s%3Afunctors). They are a handy, flexible feature that I haven't seen used in imperative system programming languages.


# Program Structure

## Descriptions and Declarations

    Description = VarDescription | ProcDescription | OtherDescriptions.

    DeclarationOrDescription  = VarDeclaration | ProcDeclaration | OtherDescriptions.

    OtherDescriptions = Inclusion | ConstDescription | TypeDescription.

A *description* names and describes a data type, procedure, variable, module or constant. A description may be given more than once; descriptions with the same name must have the same type.

A *declaration* is a description that also defines objects. An *object* is variable data or procedure code that will be included in an executable program. A declaration can only be made once.

## Modules and Interfaces

    Interface = "interface" NAME "="
                {Description ";"}
                "end" NAME ".".

    Module = "module" NAME "="
             {DeclarationOrDescription ";"}
             "end" NAME ".".

An interface contains a set of descriptions.

A module contains a set of descriptions and declarations. If there is an interface with the same name then the module implicitly contains that interface's descriptions.

All interfaces and modules implicitly contain a set of *standard descriptions* supplied by the Vanilla language. For example, the type `integer` is a standard description.

### Inclusion

    Inclusion = Include | Import.
    Include   = "include" NAME ["for" NAME {"," NAME}].
    Import    = "import" NAME.

    ImportedName = ModuleName "_" NAME.
    ModuleName   = NAME.
    GlobalName   = NAME | ImportedName. 

`include` includes descriptions from other interfaces. If the `include` has a `for` clause then only a selection of its descriptions are included. 

`import` includes descriptions from other interfaces, but each description is given an *imported name*, which is the description's name prefixed with the name of the interface. 

A module or interface's *global names* are the names of all its descriptions.


**Example**

    interface String =
        include Types for char;
        type T = array of char;
        procedure Length (s: T) : integer;
    end String.

    module String =
        import Character;
        type T = array of char;
        procedure Length (s: T) : integer =
            for i := 0 until len(s) do
                if s[i] = Character_NUL then return i end
            end;
            return len(s)
        end Length;
    end String.

## Programs

A *program* is a module that contains a procedure declaration named `main`, which will be the first procedure to be executed.  

**Example**

    module Program =
        import Args;
        import IO;
        procedure main () =
            expect(Args_argc >= 1);
            IO_Writeln(Args_argv[0])
        end main
    end Program.


# Constants

    Constant = Expression.

    ConstDescription = "const" NAME "=" Constant.

A Constant is an Expression that is evaluated by the compiler. The declared length of an array is example of an expression that must be constant.  The only names allowed in a constant expression are the names of other constants and calls to standard procedures.

A ConstDescription names a constant. A named constant may be described more than once, but the additional descriptions must evaluate to the same value.


# Variables

    VarDescription = ("var" | "val") VariableList.
    VarDeclaration = VarDescription [":=" StructuredConstant].

    VariableList = NameList ":" Type.
    NameList     = NAME {"," NAME}.

All of the variables named in the variable list of a VarDeclaration are initialized to the values in the VarDeclaration's structured constant. 

`val` declares a *immutable variable*, a variable that can only be assigned once when it is declared. *The compiler may arrange for immutable global variables to be stored in ROM.*

## Implicit Variable Declarations

A variable description has an implicit declaration if one is not given in a program's modules. 

An implicit variable declaration has a default value. Numeric variables are initialized to zero. Reference values are initialized to `nil`. Procedure values are initialized to a procedure that causes an *uninitialized procedure* runtime error. The elements of arrays and records are recursively initialized by these rules. I.e. every non-structured value in a default structure ends up being zero, nil or an error procedure.

The above rule is also used to initialize local variables within procedure bodies.

*How uninitialized procedure runtime errors are handled is implementation-dependant behaviour.*


## Structured Constants

A structured constant can be used to initialize variables of any type, including arrays and records. The value of a structured constant will become an object in the executable program.

    StructuredConstant = Constant | StructureList.
    StructureList      = "[" StructureItems {"," StructureItems} "]".
    StructureItems     = StructuredConstant ["for" Constant].

A Structure list can be assigned to a record or array variable. Each item from a structure list is assigned to
an element of the record or array in order. For records that is that order used its description. If those
elements are records or arrays then this rule is applied recursively.

A `for` clause indicates that an item should be repeated a number of times within its structure list.

A string literal can be used to declare a byte array. If it is shorter than the array then it is padded with zeros.

**Example** This array contains a one, three sevens and a six:

    var sevens: array 7 of integer := [1, 7 for 3, 6];

**Example** This array contains the bytes [64, 90, 64, 90, 0, 0, 0, 0]:

    var bytes: array 8 of byte := "AZAZ";


# Types

    TypeDescription = "type" NAME "=" Type.

    Type = GlobalName
         | "array" [DimensionList] "of" Type
         | "record" VariableList {";" VariableList} "end"
         | "ref" Type
         | "procedure" ProcType.

    DimensionList = Constant {"," Constant}.

Arrays begin at element 0. An array with more than one length in its dimension list describes arrays of arrays. I.e. `array a, b, c of t` stands for `array a of array b of array c of t`. An array with no dimension list is an *open array*. An open array is one dimensional, and its length can be found using the standard procedure `len`. An open array type may only be used as the type of a parameter or as the target of a reference type.

A reference type may refer to the name of a previously undescribed type. That type must be described later in the same module.

# Procedures

    ProcDescription = "procedure" NAME ProcType.
    ProcDeclaration = ProcDescription ["=" Body "end" NAME].

    ProcType   = "(" [Parameters {";" Parameters}] ")" [ReturnType]
    Parameters = ["var"] VariableList.
    ReturnType = ":" Type

The parameter names in procedure descriptions are placeholders for describing each parameter. They are not examined when determining type equivalence. However, parameters names are significant in procedure declarations.

A procedure with a return type is a *function procedure*. A procedure without a return type is a *proper procedure*. A function procedure may only be used in an expression. A proper procedure may only be used in a procedure call statement.

Assigning to a `var` parameter assigns to the parameter supplied by the procedure call, i.e. `var` parameters are passed by reference. Parameters without `var` are *value parameters*. Value parameters are immutable. *The compiler may pass record and array value parameters by reference.*

An array of any length may be passed to an *open array* parameter if their element types are the same. 

# Statements

    Body = Statement {";" Statement}.

    Statement = LocalDescription
              | Assignment | ProcedureCall | If | Exit | Return | Case | Empty.

Statements appear in the bodies of procedures and within other statements.

## Local Declarations

    LocalDescription = LocalVarDeclaration | ConstDescription. 
    LocalVarDeclaration = ("var" | "val") NameList (":" Type [":=" Expression] | ":=" Expression).

Variables and constants defined in a Body are only valid within that body, i.e. bodies are scopes. Variables and constants are only visible to the statements that come after their declaration statements. 

If a local variable declaration has an initializer expression then the expression is evaluated first and then all the variables named in its list are assigned that value, otherwise it is initialized to a default value by the same rules used to initialize global variables. If a local declaration has an initializer expression but no type then it takes on the type of its initializer. `val` declares a *immutable variable*, a variable that can only be assigned once when it is declared.  

A local description may not have the same name as a description from the module or any surrounding body.i .e. names may not be shadowed.

## Assignments

    Assignment = Designator {"," Designator} ":=" Expression

The expression is evaluated once then its value is assigned to each designator in the list. The designators are evaluated in order after the expression. The designators must have the same type as the expression, with two exceptions: a `byte` expression can be assigned to `integer` designator; an `integer` constant in the range 0 to 255 may be assigned to a `byte` designator.

Records of the same type and arrays of the same type and length may by assigned to each other.


## Procedure Calls

    ProcedureCall = Designator "(" [Expression {"," Expression}] ")"

The designator part of a procedure call statement must designate a proper procedure. 

The list of expressions in a procedure call are passed to the designated procedure as parameters. A `var` parameter must be passed a designator of the same type. A `val` parameter may be passed any expression, following the same rules as assignment.


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
        for i := 0 until len(string) while string[i] # 0 do
            if (string[i] >= 'A') and (string[i] <= 'Z') then
                string[i] := low(string[i] - 'a' + 'A')
            end
        end
    end uppercase;


## Exit Statements

    Exit = "exit" [NAME]

`exit` exits a loop statement. Either the loop that is named, or the innermost loop if no name is given. An exit statement can only appear inside a loop statement. A named exit statement can only appear inside a loop statement with the same name. 


## Return Statements

    Return = "return" [Expression].

`return` returns from a procedure immediately. If the procedure has a return type specified in its ProcDescription then a return value must be supplied, and the procedure's execution must end with a return statement in every case.


## Case statements

    Case   = "case" Expression "of" {Branch} ["else" Body] "end".
    Branch = "|" Range {"," Range} ":" Body.
    Range  = Constant [".." Constant].

Case expressions and range constants must be integers or bytes. All constants in a `case` statement must be unique and ranges must not overlap. If the expression's value is within a branch's ranges then that branch's Body is executed. If the value does not match a branch and there is an `else` clause then its body is executed; if there is no `else` clause then nothing is done.

*The highest label constant must be less than 256 higher that the lowest constant. Case statements are most useful when implemented using jump tables, and there must be some limit to the size of those tables.*

## Empty statement

    Empty = .

The main purpose of the empy statement is to allow superflous semicolons in a body, e.g. after the final statement.

# Expressions

    Expression = Conjunction {"or" Conjunction}. 
    Conjunction = Relation {"and" Relation}.
    Relation = Sum [RelationOp Sum].
    Sum  = Term {AddOp Term}.
    Term = Factor {MulOp Factor}.

    AddOp  = "+" | "-".
    MulOp  = "*" | "/" | "mod".
    RelationOp = "=" | "#" | ">" | "<" | ">=" | "<=".

    Factor = UnaryOp Factor
           | Designator
           | Literal
           | Conditional
           | "(" Expression ")".

    UnaryOp = "+" | "-" | "not".

## Operators

| Operators                 | Operand   | Operand   | Result    |
|---------------------------|-----------|-----------|-----------|
| `+` `-` `*` `/`           | *NumType* | *NumType* | *NumType* |
| `mod`                     | `integer` | `integer` | `integer` |
| unary `-` `+`             | *NumType* |           | *NumType* |
| `=` `#` `<` `<=` `>` `>=` | *NumType* | *NumType* | `boolean` |
| `=` `#` `<` `<=` `>` `>=` | `byte`    | `byte`    | `boolean` |
| `=` `#`                   | *RefType* | *RefType* | `boolean` |
| `and` `or`                | `boolean` | `boolean` | `boolean` |
| `not`                     | `boolean` |           | `boolean` |

*NumType* is `integer` or `real`.*RefType* is any reference type. Operands and results must have the same type, with one exception: `byte` operands will be automatically promoted to `integer`. Therefore arithmetic on `byte` values is allowed, but yields `integer` results.

`x / y` and `x mod y` may raise an runtime error if *y* = 0. How that runtime error is handled is implementation-dependant behaviour.

### Logical operators

The `and` and `or` operators are "shortcut operators", they are equivalent to these conditional expressions:

`a or b`   ≡  `if a then true else b end`

`a and b`  ≡  `if a then b else false end`

### Relational operators

Relational operators compare `integer`, `byte`, `real` and reference types. They return `boolean` values. References may only be compared for equality and inequality. Two references are equal if they refer to the same variable or both are `nil`.

## Conditional expressions

    Conditional  = "if" Expression "then" Expression
                   {"elsif" Expression "then" Expression}
                   "else" Expression
                   "end".

The expressions following `then` and `else` must have the same type.

## Designators, Procedure Calls

    Designator = GlobalName {Selection | Subscript | Dereference | Call}.

    Selection   = "." NAME.
    Subscript   = "[" Expression {"," Expression} "]".
    Dereference = "^".
    Call        = "(" [Expression {"," Expression}] ")"

Reference values are automatically dereferenced when they are the designator of a call, selection or subscript.

The list of expressions in a call are supplied to the designated procedure as parameters. A `var` parameter must be supplied with a designator. A supplied parameter must match its parameter's type, with one exception: a `byte` value will be accepted as an `integer` value parameter. 


## Literals

    Literal = INTEGER | REAL | CHARACTER | STRING.

    INTEGER  = DIGITS
             | "0x" HEXDIGIT {HEXDIGIT}
             | "0b" BINDIGIT {BINDIGIT}
             | "0o" OCTDIGIT {OCTDIGIT}.

    REAL     = DIGITS "." DIGITS [EXPONENT].
    EXPONENT = ("E" | "e") ["+" | "-"] DIGITS.

    DIGITS   = DIGIT {DIGIT}.
    DIGIT    = "0"..."9".
    BINDIGIT = "0" | "1".
    OCTDIGIT = "0"..."7".
    HEXDIGIT = "0"..."9" | "A"..."F" | "a"..."f".

The range of decimal literals is 0 to `maxint`. The range of hexadecimal, octal and binary literals is 0 to 2<sup>`lenint`</sup>-1; two's-compliment encoding is ignored. E.g. if `integer` is 16 bits wide then `0xFFFF` is equal to `-1`. This is useful when using integers to represent bit strings.

    STRING    = '"' {NORMAL | "'" | '\"' | ESCAPE} '"'.
    CHARACTER = "'" (NORMAL | '"' | "\'" | ESCAPE) "'".
    NORMAL    = " "..."~" except for "\", "'" and '"'.
    ESCAPE    = "\\" | "\n" | "\f" | "\t" | "\b" | "\0" 
              | "\x" HEXDIGIT HEXDIGIT.

String literals in expressions are anonymous immutable variables of type `array of byte`. A string literal's array has an additional element at the end containing 0. 

A character literal has a byte value; its value is the character set's code number for that character.


# Lexical Elements

Numeric and string literals have been described above.

## Names

    NAME    = LETTER {LETTER | DIGIT}.
    LETTER  = "A"..."Z" | "a"..."z".
    DIGIT   = "0"..."9".

    ImportedName = ModuleName "_" NAME.
    ModuleName   = NAME.

The underscore is reserved for prefixing imported names with module names.

## Keywords

    Keywords = 
        "and" | "array" | "by" | "byte" | "case" | "const" | "do" | "else" | "elsif"
        "end" | "exit" | "for" | "if" | "import" | "include" | "interface" | "loop"
        "mod" | "module" | "not" | "of" | "or" | "procedure" | "real" | "record"
        "ref" | "return" | "then" | "to" | "type" | "until" | "val" | "var" | "while".

## Whitespace and comments

    WHITESPACE = SPACER {SPACER}.
    SPACER     = COMMENT | " " | CR | LF | TAB.
    COMMENT    = "//" {" "..."~" | TAB} (CR | LF).

Adjacent names and keywords must be separated by whitespace. Whitespace is allowed anywhere except inside lexical elements (syntactic elements between double quotes and elements with all-uppercase names). Comments begin with `//` and end at the end of the line. Comments are allowed anywhere that whitespace is allowed.

## Source files

    SourceFile = (Interface | Module) {Interface | Module}.

A Vanilla source file contains one or more interfaces or modules. The names of the files are not significant, but the file extension `.van` should be used by convention.


# The Standard Descriptions

The standard descriptions are implicitly included at the start of every interface and module. Consequently, their names cannot be used for other purposes.

## Standard Types

| Name      | Contents                                                   |
|-----------|------------------------------------------------------------|
| `boolean` | The logical values `true` or `false`.                      |
| `integer` | Two's-complement signed integers.                          |
| `byte`    | Integers between 0 and 255. Also used to store characters. |
| `real`    | Floating-point numbers.                                    |

The floating-point number representation is implementation-dependant.

A `byte` value may be assigned to an `integer` designator or `integer` value parameter. 

`integer` is assumed to be wide enough to contain the bits of a memory address.


## Standard Constants

| Name     | Value                                                             |
|----------|-------------------------------------------------------------------|
| `minint` | the lowest possible integer value                                 |
| `maxint` | the highest possible integer value                                |
| `lenint` | the number bits required to store an integer                      |
| `nil`    | is the value of ref variables that are not pointing to variables. |
| `true`   |                                                                   |
| `false`  |                                                                   |

The constant `nil` may be assigned to any reference variable. A variable containing `nil` must not be dereferenced.

The values of `minint`, `maxint` and `lenint` are implementation-dependant.

## Standard Procedures

The standard procedures are operators that resemble procedure calls. Standard procedures may be used within constant expressions. 

In the following  tables *SimpleType* is an `integer`, `byte`, `real` or `boolean` value; *IntType* is an `integer` or `byte` value; *IntVar* is an `integer` or `byte` variable; *IntConst* is an `integer` or `byte` constant; *Array* is any array variable.

| Name            | Argument type             | Result type   | Function                             |
|-----------------|---------------------------|---------------|--------------------------------------|
| `abs`(x)        | x: NumberType             | NumberType    | absolute value of *x*                |
| `dec`(v)        | v: IntVar                 |               | v := v - 1                           |
| `dec`(v, n)     | v: IntVar; n: IntType     |               | v := v - n                           |
| `inc`(v)        | v: IntVar                 |               | v := v + 1                           |
| `inc`(v, n)     | v: IntVar; n: IntType     |               | v := v + n                           |
| `len`(v, n)     | a: Array; n: IntConst     | `integer`     | length of dimension *n* of array *a* |
| `len`(a)        | a: Array                  | `integer`     | equivalent to len(v, 0)              |

`inc` and `dec` evaluate their variable parameter only once.

`len(a, 0)` is the length of the first dimension of array *a*.

### Type transfer procedures

| Name     | Argument type           | Result type | Function                             |
|----------|-------------------------|-------------|--------------------------------------|
| `int`(b) | b: `boolean`            | `integer`   | 1 if *b* is true, otherwise 0        |
| `int`(r) | r: `real`               | `integer`   | the largest integer less than *r*    |
| `int`(i) | i: IntType              | `integer`   | the integer *i*                      |
| `flt`(i) | i: IntType              | `real`      | *i* as a real number                 |
| `low`(x) | x: SimpleType           | `byte`      | int(*x*) as a byte, if 0 ≤ int(*x*) ≤ 255 |

`low(x)` may raise an runtime error if 0 > *x* > 255. How runtime errors are handled is implementation-dependant behaviour.

### Bit Manipulation Procedures

| Name         | Argument type             | Result type | Function                       |
|--------------|---------------------------|-------------|--------------------------------|
| `lnot`(x)    | x: IntType                | IntType     | bitwise logical NOT            |
| `land`(x, y) | x, y: IntType             | IntType     | bitwise logical AND            |
| `lor`(x, y)  | x, y: IntType             | IntType     | bitwise logical inclusive-OR   |
| `lxor`(x, y) | x, y: IntType             | IntType     | bitwise logical exclusive-OR   |
| `shl`(x, n)  | x: `integer`; n: `integer` | `integer`  | left-shift bits of *x* by *n*  |
| `shr`(x, n)  | x: `integer`; n: `integer` | `integer`  | right-shift bits of *x* by *n* |
| `sha`(x, n)  | x: `integer`; n: `integer`| `integer`   | arithmetic right-shift bits of *x* by *n* |
| `bshl`(x, n) | x: `byte`; n: `integer`   | `byte`      | left-shift bits of byte *x* by *n*  |
| `bshr`(x, n) | x: `byte`; n: `integer`   | `byte`      | right-shift bits of byte *x* by *n*  |

The bit shift operators will shift in the opposite direction if *n* is negative. Shifting by more than the width of *x* results in 0, or -1 in the case of an arithmetic right-shift. 

### Memory allocation procedures

| Name         | Argument type                       | Result type | Function                          |
|--------------|-------------------------------------|-------------|-----------------------------------|
| `new`(T)     | T = `ref` T₂                        | T           | allocate an object                |
| `new`(A, d)  | A = `ref array of` T₂; d: `integer` | A           | allocate an array of *d* elements |
| `free`(r)    | r: `ref` T₂                         |             | free an object                    |

The `new` procedure calls `ALLOCATE(SYSTEM_TYPESIZE(T₂))` or `ALLOCATE(SYSTEM_TYPESIZE(T₂) * d)` to obtain the address of free space for a new variable. If that address is 0 then an runtime error is raised, otherwise the new variable is assigned a default initial value and a reference to it is returned.

The `free(r)` procedure calls `DEALLOCATE(SYSTEM_TYPE(r, integer))` to mark the space at *r* as free for reallocation.

    procedure ALLOCATE (size: integer): integer;
    procedure DEALLOCATE (address: integer);

These `ALLOCATE` and `DEALLOCATE` procedure descriptions must be included in any module that calls `new` or `free`. How the procedures are implemented is up to the programmer. They will typically be included from the interface of a module that manages memory on a heap. 

`new` and `free` may not be used in constant expressions.

### Halting procedures

| Name            | Argument type  | Result type   | Function                          |
|-----------------|----------------|---------------|-----------------------------------|
| `halt`(n)       | n: IntType     |               | halt with exit code *n*           |
| `assert`(x)     | x: `boolean`   |               | raise runtime error if not *x*    |
| `expect`(x)     | x: `boolean`   |               | raise runtime error if not *x*    |

 `assert` is for testing if the program is correct. `expect` is for testing whether the program can continue, e.g. testing whether an operating system service is still functioning. *The execution of `assert` may optionally be turned off by the compiler.*

How runtime errors and exit codes are handled is implementation-dependant behaviour.

**Example**

    assert(String_length(text) > 0);    // The program created text.
    status := Cstdio_fputs(text, file);
    expect(status # Cstdio_EOF);        // The I/O system is working.
    halt(0);                            // The program is finished now.


# The SYSTEM Interface

Including the interface `SYSTEM` allows a set of "unsafe" standard procedures to be used. Unsafe procedures access computer hardware or circumvent the type system. A module that includes `SYSTEM` should be considered unsafe. An unsafe module may have a safe interface.

If a particular computer requires language extensions, e.g. procedures that access CPU registers, then they should be added to `SYSTEM`.

In the following table *ram* refers the computer's random access memory, addressed by byte, and *AnyType* is a variable any type. 

|  Name         |  Parameter types         | Result type   |  Function                                |
|---------------|--------------------------|---------------|------------------------------------------|
| `ADDRESS`(v)  | v: AnyType               | `integer`     | address of variable *v*                  |
| `MOVE`(a,b,n) | a, b, n: `integer`       |               | move *n* bytes from *ram[a]* to *ram[b]* |
| `GET`(a, v)   | a: `integer`; v: AnyType |               | fill *v* with the bytes starting at *ram[a]*   |
| `PUT`(a, v)   | a: `integer`; v: AnyType |               | move the bytes of *v* to *ram[a]*        |
| `SIZE`(v)     | v: AnyType               | `integer`     | number of bytes in variable *v*          |
| `TYPESIZE`(T) | T = AnyType              | `integer`     | number of bytes required by type *T*     |
| `TYPE`(x, T)  | x: AnyType; T = AnyType  | T             | give *x* the type *T*                    |
| `REF`(v)      | v: AnyType               | `ref` AnyType | reference to an object                   |

`TYPE` changes the type of a value or variable without altering the underlying bits that represent it. E.g. it can be used to represent a reference as an integer or a record as an array of bytes.

**Example**

    interface IntegerRepresentation =
        procedure EndianReversal (x: integer) : integer;
    end IntegerRepresentation.

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
        end EndianReversal;
    end IntegerRepresentation.
