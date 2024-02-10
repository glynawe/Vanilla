# Vanilla  [Draft]

This is a language in the Pascal family, the starting point of its design was Oberon.

I have taken a different approach to describing declarations and modules. I would like to try extending this into something like Ocaml's module system, which I have not seen used in an imperative system programming language.


# Program Structure

## Descriptions and Declarations

    Description = VarDescription | ProcDescription | OtherDescriptions.

    DeclarationOrDescription  = VarDeclaration | ProcDeclaration | OtherDescriptions.

    OtherDescriptions = Inclusion | ConstDescription | TypeDescription

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

All interfaces and modules implicitly contain the descriptions of the standard library.

### Inclusion

    Inclusion = Include | Import.
    Include   = "include" NAME ["for" NAME {"," NAME}].
    Import    = "import" NAME.

    ImportedName = NAME "_" NAME.

`include` includes descriptions from other interfaces. If the `include` has a `for` clause then only a selection of its descriptions are included. 

`import` includes descriptions from other interfaces, but each description is given an ImportedName, which is the description's name prefixed with the name of the interface.


**Example**

    interface String =
        include Types for char;
        type T = array of char;
        procedure Length (const s: T) : integer;
    end String.

    module String =
        import Character;
        type T = array of char;
        procedure Length (const s: T) : integer =
            for i := 0 until len(s) do
                if s[i] = Character_NUL then return i end
            end;
            return len(s)
        end Length;
    end String.

## Programs

A program is a module that contains a procedure object named `main`, which will be the first procedure to be executed. A program may not include the interface of another program. 

**Example**

    module Program =
        import Args;
        import IO;
        procedure main () =
            assert(Args_argc >= 1);
            IO_Writeln(Args_argv[0])
        end main
    end Program.


# Constants

    Constant = Expression.

    ConstDescription = "const" NAME "=" Constant.

A Constant is an Expression that is evaluated by the compiler. The declared length of an array is example of an expression that must be constant.  

The only names allowed in a constant expression are the names of other constants and calls to standard procedures, which the compiler will have the means to evaluate. There is one exception: the procedure `SYSTEM_REF` may be used the create a reference to a variable. If that variable has subscripts then they must be constants.

A ConstDescription names a constant. A named constant may be described more than once, but the additional descriptions must evaluate to the same value.


# Variables

    VarDescription = "var" VariableList.
    VarDeclaration = VarDescription [":=" StructuredConstant].

    VariableList = NAME {"," NAME} ":" Type.

All of the variables named in the VariableList of a VarDeclaration are initialized to the values in the VarDeclaration's StructuredConstant.

## Implicit Variable Declarations

A variable description has an implicit declaration if one is not given in its module. 

An implicit variable declaration has a default value. Numeric variables are initialized to zero. Reference values are initialized to `nil`. Procedure values are initialized to a procedure that causes an *uninitialized procedure* exception. The elements of arrays and records are recursively initialized by these rules. I.e. every non-structured value in a default structure ends up being zero, nil or an error procedure.

*How uninitialized procedure exceptions are handled is implementation-dependant behaviour.*


## Structured Constants

A structured constant can be used to initialize variables of any type, including arrays and records. The value of a structured constant will become an object in the executable program.

    StructuredConstant = Constant | StructureList.
    StructureList      = "[" StructureItems {"," StructureItems} "]".
    StructureItems     = StructuredConstant ["for" Constant].

A Structure list can be assigned to a record or array variable. Each item from a structure list is assigned to
an element of the record or array in order. For records that is that order used its description. If those
elements are records or arrays then this rule is applied recursively.

A `for` clause indicates that an item should be repeated a number of times within its structure list.

**Example** This array contains a one, three sevens and a six:

    var sevens: array 7 of integer := [1, 7 for 3, 6];

A string literal can be used to declare a byte array. If it is shorter than the array then it is padded with zeros.

**Example** This array contains the bytes [64, 90, 64, 90, 0, 0, 0, 0]:

    var bytes: array 8 of byte := "AZAZ";


# Procedures

    ProcDescription = "procedure" NAME ProcType.
    ProcDeclaration = ProcDescription ["=" Body "end" NAME].

    ProcType   = "(" [Parameters {";" Parameters}] ")" [ReturnType]
    Parameters = ["var" | "const"] VariableList.
    ReturnType = ":" Type

The parameter names in procedure descriptions are placeholders for describing each parameter. They are not examined when determining type equivalence. However, parameters names are significant in procedure declarations.

Assigning to a `var` parameter assigns to the parameter supplied by the procedure call, i.e. `var` parameters are passed by reference. A `const` parameter is a `var` that may not be assigned to. Parameters that are neither `const` or `var` are *value parameters*. Value parameters are assigned to temporary variables in the procedure, i.e. they are pass-by-value.

A supplied parameter must match its parameter type, with one exception: a `byte` value will be accepted as an `integer` value parameter.

The compiler may pass structured type `const` parameters by reference. *The compiler may optionally disallow record and array value parameters.*

A procedure without a return type has the *statement type* which is compatible with no other type. Such a procedure may only be used as a statement.

# Types

    TypeDescription = "type" NAME "=" Type.

    Type = NAME
         | "array" [DimensionList] "of" Type
         | "record" VariableList {";" VariableList} "end"
         | "ref" Type
         | "procedure" ProcType.

    DimensionList = Constant {"," Constant}.

Arrays begin at element 0. An array with more than one length in its dimension list describes arrays of arrays. I.e. `array a, b, c of t` stands for `array a of array b of array c of t`. An array with no dimension list is an *open array*. An open array is one dimensional, and its length can be found using the standard procedure `len`. An open array type may only be used as the type of a procedure parameter or as the target of a reference type.

A reference type may refer to the name of a previously undescribed type. That type must be described later in the same module.

# Statements

    Body = Statement {";" Statement}.

    Statement = LcaleDescription
              | CallOrAssignment | If | Exit | Return | Case | Empty.

Statements appear in the bodies of procedures and within other statements.

## Local Declarations

    LcaleDescription = ConstDescription | LocalVarDeclaration. 
    LocalVarDeclaration = "var" VariableList [":=" Expression].

Variables and constants defined in a Body are only valid within that body, i.e. bodies are scopes. Variables and constants are only visible to the statements that come after their declaration statements. 

If a LocalVarDeclaration has an initializer Expression then the Expression is evaluated first and then all the variables named in the VariableList are assigned that value. Otherwise it is initialized to a default value by the same rules used to initialize global variables.

A local description may not have the same name as a description from the module or any surrounding body.i .e. names may not be shadowed.

*The compiler may optionally disallow uninitialized reference and procedure variables.*

## Call and Assignment Statements

    CallOrAssignment = Designator [ {"," Designator} ":=" Expression ]

A designator with the statement type is a procedure call statement.

A statement that is a list of Designators and an Expression is an assignment. The expression is evaluated once then its value is assigned to each designator in the list. The designators are evaluated after the expression. The designators must have types that are *assignment compatible* with the expression's type.

Records of the same type and arrays of the same type and length may by assigned to each other.

A string literal can be assigned to a byte array. If it is shorter than the array then it is padded with zeros.

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

If a loop statement has a `for` clause then its name is declared as an integer variable in the  statement's body. That variable may not be assigned to. If there is a `while` clause then the variable may be used in that clause's expression. The limiting expressions of a `for` clause are evaluated only once.

If `to` is used in a `for` clause then the loop ends when the limiting expression is exceeded. If `until` is used in a `for` clause then the loop ends when the limiting expression is reached. `for i := 0 to 4 do print(i) end` would print `0 1 2 3 4` but `for i := 0 until 4 do print(i) end` would print `0 1 2 3`

**Example**

    procedure uppercase (var string: array of byte) =
        for i := 0 until len(string) while string[i] # 0 do
            if (string[i] >= 'A') and (string[i] <= 'Z') then
                string[i] := string[i] - 'a' + 'A'
            end
        end
    end uppercase


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

Case expressions and label constants must be integer or bytes. All Constants in a `case` statement must be unique and Ranges must not overlap. If the Expression's value is within a branch's ranges then the branch's Body is executed. If the value does not match a branch and there is an `else` clause then its body is executed; if there is no `else` clause then nothing is done.

*The highest label constant must be less than 256 higher that the lowest constant. A case is most useful when implemented using a jump table, but there must be some limit to the size of those tables.*

*The case statement could be omitted to allow a simpler compiler.*

## Empty statement

    Empty = .

# Expressions

    Expression = Sum [Relation Sum].
    Sum  = Term {AddOp Term}.
    Term = Factor {MulOp Factor}.

    AddOp  = "+" | "-" | "or".
    MulOp  = "*" | "/" | "mod" | "and".
    Relation = "=" | "#" | ">" | "<" | ">=" | "<=".

    Factor = UnaryOp Factor
           | Designator
           | Literal
           | Conditional
           | "(" Expression ")".

    UnaryOp = "+" | "-" | not.

## Operators

| Operators                 | Operand   | Operand   | Result    |
|---------------------------|-----------|-----------|-----------|
| `+` `-` `*` `/`           | *NumType* | *NumType* | *NumType* |
| `mod`                     | *IntType* | *IntType* | *IntType* |
| unary `-` `+`             | *NumType* |           | *NumType* |
| `=` `#` `<` `<=` `>` `>=` | *NumType* | *NumType* | `boolean` |
| `=` `#`                   | *RefType* | *RefType* | `boolean` |
| `and` `or`                | `boolean` | `boolean` | `boolean` |
| `not`                     | `boolean` |           | `boolean` |

*IntType* is `integer` or `byte`. *NumType* is `real`, `integer` or `byte`. *RefType* is any reference type. The operand and result types must be the same, with one exception: a `byte` operand will be automatically promoted to `integer` if the other operand is `integer`.

`x / y` and `x mod y` may raise an exception if *y* = 0. How that exception is handled is implementation-dependant behaviour.

### Logical operators

The `and` and `or` operators are "shortcut operators", they are equivalent to these conditional expressions:

`a or b`   ≡  `if a then true else b end`

`a and b`  ≡  `if a then b else false end`

### Relational operators

Relational operators compare `integer`, `byte`, `real` and reference types. They return `boolean` values.

References may only be compared for equality and inequality. Two references are equal if they refer to the same variable or both are `nil`.

## Conditional expressions

    Conditional  = "if" Expression "then" Expression
                   {"elsif" Expression "then" Expression}
                   "else" Expression
                   "end".

The expressions following `then` and `else` must have the same type.

## Designators, Function Procedure Calls

    Designator = GlobalName {Selection | Subscript | Dereference | Call}.

    Selection   = "." NAME.
    Subscript   = "[" Expression {"," Expression} "]".
    Dereference = "^".
    Call        = "(" [Expression {"," Expression}] ")"

Reference values are automatically dereferenced when they are the designator of a Call, Selection or Subscript.


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

    STRING    = '"' {NORMAL | "'" | '\"' | ESCAPE} '"'
    CHARACTER = "'" (NORMAL | '"' | "\'" | ESCAPE) "'"
    ESCAPE    = "\\" | "\n" | "\f" | "\t" | "\b" | "\0" | "\x" HEXDIGIT HEXDIGIT
    NORMAL    = " "..."~" except for "\", "'" and '"'

String literals in Expressions are anonymous variables of type `array of byte`. A string literal's array has an additional element at the end containing 0. String literals cannot be passed as `var` parameters. The procedure `SYSTEM_REF` may not be used on a string constant.

A character constant has a byte value; its value is the character set's code number for that character.


# Names

    NAME    = LETTER {LETTER | DIGIT | "_"}
    LETTER  = "A"..."Z" | "a"..."z".
    DIGIT   = "0"..."9".


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

A `byte` value may be assigned to an `integer` variable or `integer` value parameter.

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

The constant `nil` may be assigned to any reference variable. A variable containing `nil` must not be dereferenced. *A compiler may optionally disallow the use of `nil` in a module.*

The values of `minint`, `maxint` and `lenint` are implementation-dependant.

## Standard Procedures

The standard procedures are operators that resemble procedure calls. Standard procedures may be used within constant expressions. 


In the following  tables *NumberType* is an integer, byte or real value; *IntType* is integer or byte value; *Array* is any array variable; *AnyType* is a variable any type; *IntVar* is an integer variable; *IntConst* is an integer constant.

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

### Halting procedures

| Name            | Argument type  | Result type   | Function                      |
|-----------------|----------------|---------------|-------------------------------|
| `exit`(n)       | n: `integer`   |               | halt with exit code *n*       |
| `assert`(x)     | x: `boolean`   |               | raise exception if not *x*    |
| `expect`(x)     | x: `boolean`   |               | raise exception if not *x*    |

 `assert` is for testing if the program is correct. `expect` is for testing whether the program can continue, e.g. testing whether an operating system service is still functioning. *The execution of `assert` may optionally be turned off by the compiler.*

How exceptions and exit codes are handled is implementation-dependant behaviour.

**Example**

    assert(String_length(text) > 0);    // The program must create text.
    status := Cstdio_fputs(text, file);
    expect(status # Cstdio_EOF);        // The I/O system should be working.
    exit(0);                            // The program is finished now.

### Type transfer procedures

| Name     | Argument type           | Result type | Function                             |
|----------|-------------------------|-------------|--------------------------------------|
| `int`(b) | b: `boolean`            | `integer`   | 1 if *b* is true, otherwise 0        |
| `int`(r) | r: `real`               | `integer`   | the largest integer less than *r*    |
| `int`(i) | i: IntType              | `integer`   | the integer *i*                      |
| `flt`(i) | i: IntType              | `real`      | *i* as a real number                 |
| `low`(x) | x: NumberType           | `byte`      | int(*x*) as a byte, if 0 ≤ *x* ≤ 255 |

`low(x)` may raise an exception if 0 > *x* > 255. How exceptions are handled is implementation-dependant behaviour.

### Bit Manipulation Procedures

| Name         | Argument type             | Result type | Function                       |
|--------------|---------------------------|-------------|--------------------------------|
| `lnot`(x)    | x: IntType                | IntType     | bitwise logical NOT            |
| `land`(x, y) | x, y: IntType             | IntType     | bitwise logical AND            |
| `lor`(x, y)  | x, y: IntType             | IntType     | bitwise logical inclusive-OR   |
| `lxor`(x, y) | x, y: IntType             | IntType     | bitwise logical exclusive-OR   |
| `shl`(x, n)  | x: IntType; n: `integer`  | IntType     | left-shift bits of *x* by *n*  |
| `shr`(x, n)  | x: IntType; n: `integer`  | IntType     | right-shift bits of *x* by *n* |
| `sha`(x, n)  | x: IntType; n: `integer`  | IntType     | arithmetic right-shift bits of *x* by *n* |

The bit shift operators will shift in the opposite direction if *n* is negative. Shifting by more than the
width of *x* results in 0, or -1 in the case of an arithmetic right-shift.  

### Memory allocation procedures

| Name         | Argument type                       | Result type | Function                          |
|--------------|-------------------------------------|-------------|-----------------------------------|
| `new`(T)     | T = `ref` T₂                        | T           | allocate an object                |
| `new`(A, d)  | A = `ref array of` T₂; d: `integer` | A           | allocate an array of *d* elements |
| `free`(r)    | r: `ref` T₂                         |             | free an object                    |

The `new` procedure calls `ALLOCATE(SYSTEM_SIZE(T₂))` or `ALLOCATE(SYSTEM_SIZE(T₂) * d)` to obtain the address of free space for a new variable. If that address is 0 then an exception is raised, otherwise the new variable is assigned a default initial value and a reference to it is returned.

The `free(r)` procedure calls `DEALLOCATE(SYSTEM_TYPE(r, integer))` to mark the space at *r* as free for reallocation.

    procedure ALLOCATE (size: integer): integer;
    procedure DEALLOCATE (address: integer);

These `ALLOCATE` and `DEALLOCATE` procedure descriptions must be included in any module that calls `new` or `free`. How the procedures are implemented is up to the programmer. They will typically be included from the interface of a module that manages memory on a heap. 


# The SYSTEM Interface

Including the interface `SYSTEM` allows a set of "unsafe" standard procedures to be used. Unsafe procedures access computer hardware or circumvent the type system. A module that includes `SYSTEM` should be considered unsafe. An unsafe module may have a safe interface.

If a particular computer requires language extensions, e.g. procedures that access CPU registers, then they should be added to `SYSTEM`.

In the following table *ram* refers the computer's random access memory, addressed by byte.

|  Name         |  Parameter types         | Result type |  Function                                |
|---------------|--------------------------|-------------|------------------------------------------|
| `ADDR`(v)     | v: AnyType               | `integer`   | address of variable *v*                  |
| `GET`(a, v)   | a: `integer`; v: AnyType |             | fill *v* with the bytes starting at *ram[a]*   |
| `MOVE`(a,b,n) | a, b, n: `integer`       |             | move *n* bytes from *ram[a]* to *ram[b]* |
| `PUT`(a, v)   | a: integer; v: AnyType   |             | move the bytes of *v* to *ram[a]*        |
| `SIZE`(v)     | v: AnyType               | `integer`   | number of bytes in variable *v*          |
| `SIZE`(T)     | T = AnyType              | `integer`   | number of bytes required by type *T*     |
| `TYPE`(x, T)  | x: AnyType; T = AnyType  | T           | give *x* the type *T*                    |
| `REF`(v)      | v: T                     | `ref` T     | reference to an object                   |

`TYPE` changes the type of a value or variable without altering the underlying bits that represent it. E.g. it can be used to represent a reference as an integer or a record as an array of bytes.

**Example**

    interface IntegerRepresentation =
        procedure EndianReversal (x: integer) : integer;
    end IntegerRepresentation.

    module IntegerRepresentation =
        include SYSTEM;
        procedure EndianReversal (x: integer) : integer =
            const w = SIZE(x);
            var a, b: array w of byte;
            a := TYPE(x, array w of byte)
            for i := 0 until w do
                b[i] := a[w - i - 1]
            end;
            return TYPE(b, integer)
        end EndianReversal;
    end IntegerRepresentation.
