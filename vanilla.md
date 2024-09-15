# Vanilla  [Draft]

Vanilla is an imperative systems programming language in the Algol family. Vanilla has a module system with *functors*, a feature taken from OCaml. Functors are modules that take other modules as arguments. They are a single, simple mechanism that can provide features like abstract data types, generic types, traits, dependency injection and module extension.

**A quick comparison to C.** 

- There is a true module system for defining abstract data types. 
- There is no macro system, but constants and constant expressions are part of the language. 
- Pointers cannot point to arbitrary locations, just to allocated objects. 
- Pointers are not used to implement arrays. Arrays are a type. 
- Array argument lengths are always known. 
- The pointer dereference operator is postfix.
- Types are inferred when declaring new variables. 
- There is a smaller selection of numeric types. 
- There is no automatic casting between types. 
- The `for` statement is less intricate. 
- There is a smaller number of operators, less common operations are builtin functions. 
- Functions that access hardware and circumvent the type system must be imported from the `SYSTEM` module. 

**A quick comparison to C++ and Java.**

- The units of encapsulation are modules, typically containing types and functions for ADTs.
- Nevertheless, ADT function calls resemble method calls. 
- Parameterized modules (functors) take the place of C++ templates and Java generic classes.
- Unlike generic classes, functors can supply whole groups of interrelated types.
- There is no inheritance of implementation, but inclusion of trait functions (mixins) is possible.

**A quick comparison to SML and Ocaml.**

- The 'core language' is imperative, and lower-level. 
  - Variables are assignable, functions can have call-by-reference parameters.
  - There are no closures.
- The 'module language' is simpler. 
  - Modules cannot be nested.
  - Modules, interfaces (signatures) and functors must always be named. 
- A functor instantiation can be included (opened) into a module.
- A method call-like syntax makes module name prefixes less necessary. 

# Example

This very simplified program defines strings and generic sets as abstract data types. They are then used to create sets of strings. 

    interface COMPARABLE {
        type T;
        fn Equals (a, b: T) : bool;
    }

    interface STRING {
        include COMPARABLE;
        type Repr;
        type T = ref Repr;
        fn New (text: []byte): T;
    }

    module String : STRING {
        type Repr = []byte;
        fn Equals (a: T, b: T) : bool {
            return a == b || len(a) == len(b) && a^ == b^;
        }
        fn New (text: []byte): T {
            var s = new(byte, len(text)); 
            s^ = text; 
            return s;
        }
    }

    interface SET {
        type Repr;
        type T = ref Repr;
        type ElemT;
        let Empty: T;
        fn Add (set: T, element: ElemT) : T;
        fn Includes (set: T, element: ElemT) : bool;
    }

    module Set <Element: COMPARABLE> : SET with ElemT = Element::T {
        type ElemT;
        type Repr = struct { 
            value: ElemT; 
            next: T; 
        };
        let Empty: T = null;
        fn Add (set: T, element: ElemT) : T {
            var list = new(R); list.head = head; list.tail = tail;
            return list;
        }
        fn Contains (set: T, element: ElemT) : bool {
            while (set != null) {
                if (set.head.Equals(element)) 
                    return true;
                else 
                    set = set.tail; 
            }
            return false;
        }
    }

    module Program {
        import Print;  
        import String;
        import StringSet = Set<String>;
        fn main () {
            let s = String::New("Hello World!");
            var set = StringSet::Empty;
            set = set.Add(s);
            if (set.Contains(set, s))
                Print::string("Success!");
        }
    }


# Program Structure

## Definitions and Declarations

    Definition = VarDefinition | FunctionDefinition | OtherDefinitions.

    DeclarationOrDefinition  = VarDeclaration | FnDeclaration | OtherDefinitions.

    OtherDefinitions = Inclusion | ConstDefinition | TypeDefinition.

A *definition* names and describes a data type, function, variable, module or constant. A definition may be given more than once; definitions with the same name must have the same type.

A *declaration* is a definition that also defines *object code*. Object code is variable data or function code that will be included in an executable program. A declaration can only be made once.

## Modules and Interfaces

    Program = (Interface | Module | Functor) ... .

A Vanilla program may contain any number of interfaces, modules and functors. One module must declare a function called `main`, which will be the first function to be executed.

    Interface = "interface" InterfaceName "{" 
                {Definition} 
                "}".

    Module    = "module" ModuleName [PublicInterface] "{" 
                {DeclarationOrDefinition} 
                "}".

    Functor   = "module" ModuleName "<" ModuleParameter ","... ">" 
                [PublicInterface] [TypeConstraints] "{" 
                {DeclarationOrDefinition} 
                "}".

    PublicInterface  = [":" InterfaceName].
    ModuleParameter  = ModuleName ":" InterfaceName.
    TypeConstraints  = "with" TypeEquivalence ","... 
    TypeEquivalence  = TypeName "=" TypeName.
    TypeName         = ModuleName "::" NAME.

    InterfaceName = NAME.
    ModuleName    = NAME.
    FunctorName   = NAME.

An *interface* contains a set of definitions. A *module* contains a set of definitions and declarations. The primary purpose of modules is to group together collections of types and functions to define abstract data types.

If a module is declared with a *public interface* then only the definitions in that interface will be available when the module is imported. The module must contain declarations for all the definitions in its public interface. 

A *functor* is a module parametrized by interfaces for modules that it may import; the actual modules are supplied when the functor is imported. The primary purpose of functors is to define generic abstract data types. Each interface argument specifies a minimum set of definitions that the actual module must provide. A functor *type constraint* specifies types from different argument modules that are to be equivalent (this is important when defining generic types). 

Functor application is *generative*. Modules are distinct even in their interfaces are the same. In this example `A.t` and `B.t` are incompatible types:

    interface S { type t; }
    module M <A: S, B.t: S> { ... }  // A.t ≠ B.t

However, a type constraint can be used to make `A.t` and `B.t` compatible:

    interface S { type t; }
    module M <A: S, B: S> with A.t = B.t { ... } 

A module without an explicit public interface is given a default interface that excludes its imported names.

All interfaces and modules implicitly contain a set of *standard declarations* supplied by the Vanilla language. For example, the type `int` is a standard declaration.

**Example**

    module Map <Key: Comparable, Value: ADT> 
        with KeyType = Key::Type, ValueType = Value::Type 
    {
        type MapType;
        type ValueType;
        type KeyType;
        fn Set (map: MapType, key: KeyType, value: ValueType) { ... } 
        ...
    }

### Inclusion

    Inclusion = Include | Import.
    Import    = "import" ModuleName ["=" Expansion] ";".
    Include   = "include"  Expansion ";".
    Expansion = [":" PublicInterface] FunctorName ["<" ModuleName ","... ">"] [typeconstraints]. 

    ImportedName = ModuleName "::" NAME.
    GlobalName   = NAME | ImportedName. 

`include` includes content from another module or interface. The contents of an interface are its definitions, the contents of a module are its declarations. `import` also includes content, but each definition is given an *imported name*, which is the definition's name prefixed with the name of the module. 

An `expansion` designates an existing module or interface, or it creates a new module from a functor. The functor's module arguments are replaced with the modules in the functor expansion's list of module names, and types from those modules are made equivalent according to the functor's type constraints. If a *public interface* is given then only the subset of definitions in that interface will be visible.

A module's *global names* are the names of all its definitions.

\[In Ocaml interfaces are called *module types*, in Standard ML interfaces are called *signatures*. Vanilla functors are *generative*; i.e. if two modules are made from the same functor then the abstract types that they contain are not equivalent. Vanilla modules are not *translucent*; if a concrete type definition is given inside a module but the type is abstract in its public interface to a module then that type becomes abstract.]


# Constants

    Constant = Expression.

    ConstDefinition = "const" NAME "=" Constant ";".

A *constant* is an expression that is evaluated by the compiler. The declared length of an array is an example of an expression that must be constant.  The only names allowed in a constant expression are the names of other constants and calls to standard functions.

A ConstDefinition names a constant. A named constant may be described more than once, but the additional definitions must evaluate to the same value.


# Variables

    VarDefinition = ("var" | "let") VariableList ";".
    VarDeclaration = ("var" | "let") VariableList ["=" StructuredConstant] ";".

    VariableList = IdentList ":" Type.
    IdentList     = NAME ","... .

A list of distinct variable definitions will be made if a list of names is given. `var a, b, c: t;` is shorthand for `var a: t; var b: t; var c: t;`

All of the variables named in the variable list of a VarDeclaration are initialized to the values in the VarDeclaration's structured constant. 

`let` declares a *immutable variable*, a variable that can only be assigned once when it is declared. *The compiler may arrange for immutable global variables to be stored in ROM.*

A variable definition has an implicit declaration if one is not given in a program's modules. E.g. the definition `var i: int;` will be provided the declaration `var i: int = 0;`.

## Structured Constants

A structured constant can be used to initialize global variables of any type, especially arrays and records. The value of a structured constant will become object code for the executable program.

    StructuredConstant = Constant | StructureList.
    StructureList      = "{" StructureItems ","... "}".
    StructureItems     = StructuredConstant ["for" Constant].

A structure list can be assigned to a record or array variable. Each item from a structure list is assigned to
an element of the record or array in order. For records that is that order used its definition. If those
elements are records or arrays then this rule is applied recursively.

A `for` clause indicates that an item should be repeated a number of times within its structure list.

A string literal can be used to declare a byte array. If it is shorter than the array then it is padded with zeros.

**Example** This array contains a one, three sevens and a six:

    var sevens: [5]int = {1, 7 for 3, 6};

**Example** This array contains the bytes {64, 90, 64, 90, 0, 0, 0, 0}:

    let string: [8]byte = "AZAZ";


## Implicit Variable Declarations

A variable definition has an implicit declaration if one is not given in a program's modules. 

An implicit variable declaration has a default value. Numeric variables are initialized to zero. Pointer values are initialized to `null`. The elements of arrays and records are recursively initialized by these rules. I.e. every non-structured value in a default structure ends up being zero or null.

The above rule is also used to initialize local variables within blocks.


# Types

    TypeDefinition = "type" NAME "=" Type | OpaqueType.
    OpaqueType     = "type" NAME.

    Type = GlobalName
         | "[" Constant "]" Type
         | "[" "]" Type
         | "struct" "{" {VariableList ";"} "}"
         | "ref" Type
         | "fn" FnType.

    DimensionList = Constant ","... .

Arrays begin at element 0. An array with no specified dimension is an *open array* which may have any length. An open array's length can be found using the standard function `len`. An open array type may only be used as the type of an argument or as the target of a pointer type.

A function type may only be used as the type of an argument or as the target of a pointer type.

An *opaque type* is a type whose definition is not yet given. An opaque type can be used in an interface to denote an abstract type, or in a module to allow a record type to contain pointers to itself. An opaque type must be defined before it can be used in a module, either by a full type definition or a functor type constraint.

# Functions

    FunctionDefinition = "fn" NAME FnType ";".
    FnDeclaration = ["loop"] "fn" NAME FnType (";" | Block).

    FnType     = "(" [Parameters ","...] ")" [ReturnType]
    Parameters = ["var"] VariableList.
    ReturnType = ":" Type

The argument names in function definitions are placeholders for describing each argument. They are not examined when determining type equivalence. However, arguments names are significant in function declarations.

A function with a return type is an *expression function*. A function without a return type is a *procedure function*. An expression function may only be used in an expression. A procedure function may only be used as a statement.

Assigning to a `var` argument assigns to the argument supplied by the function call, i.e. `var` arguments are passed by reference. Parameters without `var` are *value arguments*. Value arguments are immutable. *The compiler may pass record and array value arguments by reference.*

An array of any length may be passed to an *open array* argument if their element types are the same. 

A function definition can be used in a module to define it early. This allows sets of mutually recursive functions to be defined. (This is like providing a *function prototype* in C.) 

A `loop` function must be tail-call optimizable. I.e. if the function calls itself recursively then that call must be optimizable into a loop. The compiler will reject the program if it cannot perform the optimisation. 

*A value argument does not come with a guarantee that the argument will retain the same value all through the execution of its function. "Aliasing" is possible. If a global variable is given as an argument then assigning to that variable from within the function also changes the argument's value.*

# Statements

    Block = "{" {Statement} "}".

    Statement = LocalDefinition | Block | For | While | Loop
              | Assignment | FunctionCall | If | Break | Return | Switch | Empty.

    Empty = ";".

## Local Declarations

    LocalDefinition = LocalVarDeclaration | LocalLetDeclaration | ConstDefinition. 
    LocalVarDeclaration = "var" IdentList (":" Type ["=" Expression] | "=" Expression).
    LocalLetDeclaration = "let" IdentList [":" Type] "=" Expression.

Variables and constants defined in a block are only valid within that block, i.e. blocks are scopes. Variables and constants are only visible to the statements that come after their declaration statements. 

If a local variable declaration has an initializer expression then the expression is evaluated first and then all the variables named in its list are assigned that value, otherwise it is initialized to a default value by the same rules used to initialize global variables. If a local declaration has an initializer expression but no type then it takes on the type of its initializer. `let` declares a *immutable variable*, a variable that can only be assigned once when it is declared.  

A local definition may not have the same name as any definition in the same block or any surrounding block, including the function's argument names. I.e. local names may not be shadowed. 

## Assignments

    Assignment = Designator "=" Expression ";"
               | Designator MathOp "=" Expression ";"
               | Designator "++" ";"
               | Designator "--" ";"

    MathOp = "+" | "-" | "*" | "/" | "%"

The expression is evaluated  then its value is assigned to the designator. The designator must have the same type as the expression. The `++`, `--`, `+=` etc. operators have the same meaning as in C, but may only be used as statements.

Records of the same type and arrays of the same type and length may be assigned to each other.


## Function Calls

    FunctionCall = Designator "(" [Expression ","...] ")" ";"

The designator part of a function call statement must designate a procedure function. 

The list of expressions in a function call are passed to the designated function as arguments. A reference argument must be passed a designator of the same type. A value argument may be passed any expression, following the same rules as assignment.

### "Method calls"

If the start of a designator refers to a variable *v* of type *M::t*, and the last name in the designator refers to a function *M::p*, then `M::p(v, ...)` may be written as `v.p(...)`. (This is similar to the syntactic sugar that Python uses for method calls.)

**Example**

If `list.head` has type `Set::t` and there exists a function `Set::add(s: Set::t; v: vt)` then these two function calls mean the same thing:

```
Set::add(list.head, value)
list.head.add(value)
```

## If Statements

    If = "if" "(" Expression ")" Statement ["else" Statement].

*The "dangling else" ambiguity is resolved in the usual way: if there are two open `if` statements then an `else` clause attaches to the innermost one.*  

## Looping Statements

    For   = [NAME ":"] "for" "(" NAME "=" Expression  (":" | "..") Expression ")" Statement.
    While = [NAME ":"] "while" "(" Expression ")" Statement.
    Loop  = [NAME ":"] "loop" Statement.

    Break = "break" [NAME] ";".

Looping statements may be labelled with a name to be used by `break` statements. `break` exits any looping statement; either the loop that is named, or the innermost loop if no name is given. A break statement can only appear inside a looping statement. A named break statement can only appear inside a looping statement with the same name. A break statement within a `switch` statement must have a name.

A `for` loop's control variable name is an immutable integer variable in the looped statement. The limiting expressions of a `for` loop are evaluated only once. If the limits of a `for` statement are separated by `:` then the loop ends when the limiting expression is reached. If `..` is used then the loop ends when the limiting expression is exceeded. `for (i = 0 : 4) print(i);` would print `0 1 2 3` but `for (i = 0 .. 4) print(i);` would print `0 1 2 3 4`. 

A `loop` statement continues looping until an applicable `break` statement is executed.
****

**Example**

    fn uppercase (var string: []byte) {
        LOOP: for (i = 0 : len(string)) {
            switch (string[i]) {
                case 'A'..'Z': string[i] += 'A' - 'a';
                case '\0': break LOOP;
            }
        }
    }


## Switch statements

    Switch     = "switch" "(" Expression ")" "{" {Case} ["default" ":" Statements] "}".
    Case       = "case" Range ","... ":" Statements.
    Range      = Constant [".." Constant].
    Statements = Statement {Statement}

Switch expressions and switch range constants must be integers or bytes. All constants in a `case` statement must be unique and ranges must not overlap. If the expression's value is within a case's ranges then that case's statements are executed. If the value does not match a case and there is a `default` clause then its statements are executed; if there is no `default` clause then nothing is done. 

**Example**

    switch (c) {
        case '0'..'9': 
            kind = DIGIT;
        case 'a'..'z', 'A'..'Z': 
            kind = LETTER;
        case ' ', '\t', ',': 
            kind = PUNCTUATION;
        default: 
            error(); 
            kind = UNEXPECTED;
    }

*Cases do not not "fall through", `break` is not necessary.*

*The highest range constant must be less than 256 higher than the lowest constant. Switch statements are most useful when implemented using jump tables, and there must be some limit to the size of those tables.*

## Return Statements

    Return = "return" [Expression] ";".

`return` returns from a function immediately. If the function has a return type specified in its definition then a return value must be supplied, and the function's execution must end with a return statement in every case.


# Expressions

    Expression = Disjunction ["?" Disjunction ":" Expression].
    Disjunction = Conjunction {"||" Conjunction}. 
    Conjunction = Relation {"&&" Relation}.
    Relation = Sum [RelationOp Sum].
    Sum  = Term {AddOp Term}.
    Term = Factor {MulOp Factor}.
    Factor = UnaryOp Factor
           | Designator
           | FunctionCall
           | Literal
           | "(" Expression ")".

    AddOp  = "+" | "-".
    MulOp  = "*" | "/" | "%".
    RelationOp = "==" | "!=" | ">" | "<" | ">=" | "<=".
    UnaryOp = "+" | "-" | "!".

## Operators

| Operators                - | Operand   | Operand   | Result    |
|----------------------------|-----------|-----------|-----------|
| `+` `-` `*` `/`            | *NumType* | *NumType* | *NumType* |
| `%`                        | *IntType* | *IntType* | *IntType* |
| unary `-` `+`              | *NumType* |           | *NumType* |
| `==` `!=` `<` `<=` `>` `>=`| *NumType* | *NumType* | `bool`    |
| `==` `!=`                  | *RefType* | *RefType* | `bool`    |
| `&&` `||`                  | `bool`    | `bool`    | `bool`    |
| `!`                        | `bool`    |           | `bool`    |

*NumType* is `real`, `int`, `word` or `byte`. *IntType* is `int`, `word` or `byte`. *RefType* is any pointer type. Operands and results must have the same type.

`x / y` and `x % y` may raise a runtime error if *y* = 0. How that runtime error is handled is implementation-dependent behaviour.

Relational operators compare `int`, `word`, `byte`, `float` and pointer types. They return `bool` values. Pointers may only be compared for equality and inequality. Two pointers are equal if they refer to the same variable or both are `null`.

### Logical operators

*cond* `?` *expr1* `:` *expr2* is the conditional expression. If *cond* is true then *expr1* is evaluated and returned. If *cond* is false then *expr2* is evaluated and returned. *cond* must have the `bool` type, and *expr1* and *expr2* must have identical types.

The `&&` and `||` operators are "shortcut operators", they are equivalent to these conditional expressions:

`a || b`   ≡  `a ? true : b`

`a && b`  ≡  `a ? b : false`


## Designators, Function Calls

    Designator = GlobalName {Selection | Subscript | Dereference | Call}.

    Selection   = "." NAME.
    Subscript   = "[" Expression ","... "]".
    Dereference = "^".
    Call        = "(" [Expression ","...] ")"

Pointer values are automatically dereferenced when they are the designator of a call, selection or subscript. The dereferencing operator `^` will not need to be used often, but is useful when comparing or assigning the targets of pointers.

The list of expressions in a call are supplied to the designated function as arguments. A by-reference argument must be supplied with a designator. A supplied argument must match its argument's type. 

The "method call" syntax for procedure function calls may be used for expression function calls too. 


## Literals

    Literal = INTEGER | FLOAT | CHARACTER | STRING.

INTEGER literals have the type `int`. WORD literals have type `word`. BYTE literals have the type `byte`. FLOAT literals have the type `float`. STRING literals  are anonymous immutable variables of type `[]byte`. A string literal's array has an additional element at the end containing `'\0'`. 

BYTE, WORD and INTEGER literals are distinct. BYTE literals are either integer literals with the suffix `X` or character literals in single quotes. The range of BYTE literals is 0X to 255X. The range of WORD literals is 0 to `maxword`. WORD literals are integer literals with the suffix `LOWER`. 

# The standard declarations

The standard declarations are implicitly included at the start of every interface and module. Their names cannot be used for other purposes.

## Standard Types

| NAME     | Contents                                                    |
|-----------|------------------------------------------------------------|
| `bool`    | The logical values `true` or `false`.                      |
| `int`     | Two's-complement signed integers.                          |
| `word`    | Unsigned integers between 0 and `maxword`.                 |
| `byte`    | Integers between 0 and 255. Also used to store characters. |
| `float`   | Floating-point numbers.                                    |

The floating-point number representation is implementation-dependent. `int` should have a convenient range for arithmetic. `word` must be wide enough to contain a memory address.


## Standard Constants

| NAME     | Value                                                             |
|----------|-------------------------------------------------------------------|
| `minint` | the lowest possible int value                                     |
| `maxint` | the highest possible int value                                    |
| `maxword`| the highest possible word value                                   |
| `lenint` | the number of bits required to store an int                       |
| `lenword`| the number of bits required to store a word                       |
| `null`   | is the value of pointer variables that are not pointing to variables. |
| `true`   |                                                                   |
| `false`  |                                                                   |

The constant `null` may be assigned to any pointer variable. A variable containing `null` must not be dereferenced.

The values of `minint`, `maxint` and `lenint` are implementation-dependent.

## Standard Functions

The standard functions are operators that resemble function calls. Some are polymorphic, some take type definitions as arguments. Standard functions may be used within constant expressions. 

In the following tables *IntType* is an `int`, `word` or `byte` value, *NumType* is an integer type or `float`, `T` is a name of a type and *Array* is any array variable.

| Definition                         | Function                             |
|------------------------------------|--------------------------------------|
| `abs (x: int) : int`               | absolute value of `x`                |
| `abs (x: float) : float`           | absolute value of `x`                |
| `len (a: Array, n: IntConst)`      | length of dimension `n` of array `a` |
| `len (a: Array)`                   | equivalent to `len(v, 0)`            |
| `as (v: NumType, T): NumType`      | convert `v` to numeric type `T`.     |
| `fits (T, v: NumType): bool`       | true if `v` will fit in type `T`.    |


`len(a, 0)` is the length of the first dimension of array `a`.

`as` may raise a runtime error if its argument value ie outside its return type's range. `fits` can be used to determine if that will happen. How runtime errors are handled is implementation-dependent behaviour.

### Bit Manipulation Functions

| Definition                                | Function                                  |
|-------------------------------------------|-------------------------------------------|
| `lnot (x: IntType) : IntType`             | bitwise logical NOT                       |
| `land (x, y: IntType) : IntType`          | bitwise logical AND                       |
| `lor (x, y: IntType) : IntType`           | bitwise logical inclusive-OR              |
| `lxor (x, y: IntType) : IntType`          | bitwise logical exclusive-OR              |
| `shl (x: IntType, n: int) : IntType`      | left-shift bits of `x` by `n`             |
| `shr (x: IntType, n: int) : IntType`      | right-shift bits of `x` by `n`            |
| `sha (x: IntType, n: int) : IntType`      | arithmetic right-shift bits of `x` by `n` |

The bit shift operators will shift in the opposite direction if *n* is negative. Shifting by more than the width of *x* results in 0, or -1 in the case of an arithmetic right-shift. 

### Memory allocation functions

| Definition                             | Function                          |
|----------------------------------------|-----------------------------------|
| `new (T) : ref T`                      | allocate data                     |
| `new (T, d: int) : ref [] T`           | allocate an array of `d` elements |
| `free (r : ref T)`                     | free data                         |

`new` and `free` may not be used in constant expressions. The type `T` may not be an opaque type or open array (its size must be known).

#### Garbage Collection Option

The `new` function takes a type definition as its first argument, finds memory space for an anonymous variable of that type, assigns a default initial value to the variable and returns a pointer to it. If no memory space is available then a runtime error is raised. 

The `free` function does nothing. 

#### Manual Allocation Option

`new` and `free` exist to provide a type safe way to use low-level `ALLOCATE` and `DEALLOCATE` functions. `ALLOCATE` and `DEALLOCATE` function definitions must be included in any module that calls `new` or `free`. How the functions are implemented is up to the programmer. They will typically be included from the interface of a module that manages memory on a heap. 

    fn ALLOCATE (size: int): word;  // returns an address
    fn DEALLOCATE (address: word);

The `new` function calls `ALLOCATE(SYSTEM::TYPESIZE(T))` or `ALLOCATE(SYSTEM::TYPESIZE(T) * d)` to obtain the address of memory space for an anonymous variable of  type `T`. If that address is 0 then a runtime error is raised, otherwise the anonymous variable is assigned a default initial value and a pointer to it is returned.

The `free(r)` function calls `DEALLOCATE(SYSTEM::TYPE(r, int))` to mark the space at *r* as free for reallocation.

### Halting functions

| Definition            | Function                          |
|-----------------------|-----------------------------------|
| `exit (n: int)`       | halt with exit code *n*           |
| `assert (x: bool)`    | raise runtime error if not *x*    |
| `expect (x: bool)`    | raise runtime error if not *x*    |

 `assert` is for testing if the program is correct. `expect` is for testing whether the program should continue, e.g. testing whether an operating system service is still functioning. *The execution of `assert` may optionally be turned off by the compiler.*

How runtime errors and exit codes are handled is implementation-dependent behaviour.

**Example**

    assert(String::length(text) > 0);    // The program created text.
    status = Cstdio::fputs(text, file);
    expect(status != Cstdio::EOF);       // The I/O system is working.
    exit(0);                            // The program is finished now.


# The SYSTEM Interface

Including the interface `SYSTEM` allows a set of "unsafe" standard functions to be used. Unsafe functions access computer hardware or circumvent the type system. A module that includes `SYSTEM` should be considered unsafe. An unsafe module may have a safe interface.

If a particular computer requires language extensions, e.g. functions that access CPU registers, then they should be added to `SYSTEM`.

In the following table *RAM* refers to the computer's random access memory, addressed by byte; *AnyType* is any type; *T* is a type definition given as an argument.

|  Definition                          | Function                                     |
|--------------------------------------|----------------------------------------------|
| `ADDRESS (var v: AnyType) : word`    | address of variable `v`                      |
| `MOVE (a, b, n: int)`                | move `n` bytes from `RAM[a]` to `RAM[b]`     |
| `GET (a: word, var v: AnyType)`      | fill `v` with the bytes starting at `RAM[a]` |
| `PUT (a: word, v: AnyType)`          | move the bytes of `v` to `RAM[a]`            |
| `SIZE (v : AnyType) : int`           | number of bytes in variable `v`              |
| `LOC (var v: AnyType) : ref AnyType` | make a pointer to a variable or function     |
| `TYPESIZE (T)  : word`               | number of bytes required by type `T`         |
| `TYPE (x: AnyType, T) : T`           | give `x` the type `T`                        |

`TYPE` changes the type of a value or variable without altering the underlying bits that represent it. E.g. it can be used to represent a pointer as a word or a record as an array of bytes.

**Example**

    interface IntegerRepresentation {
        fn EndianReversal (x: int) : int;
    }

    module IntegerRepresentation {
        include SYSTEM;
        fn EndianReversal (x: int) : int {
            const w = SIZE(x);
            let a = TYPE(x, [w]byte);
            var b: [w]byte;
            for (i = 0 : w)
                b[i] = a[w - i - 1];
            return TYPE(b, int);
        }
    }

# Lexical Elements

## Numeric and String Literals 

    INTEGER  = DIGITS
             | "0x" HEXDIGIT {HEXDIGIT}
             | "0b" BINDIGIT {BINDIGIT}
             | "0o" OCTDIGIT {OCTDIGIT}.

    BYTE      = INTEGER "X" | CHARACTER.
    WORD      = INTEGER "LOWER".
    CHARACTER = "'" (STRCHAR | '"' | "\'" | ESCAPE) "'".

    STRING    = '"' {STRCHAR | "'" | '\"' | ESCAPE} '"'.

    FLOAT     = DIGITS "." DIGITS [EXPONENT].

    EXPONENT = ("E" | "e") ["+" | "-"] DIGITS.
    DIGITS   = DIGIT {DIGIT}.
    DIGIT    = "0"..."9".
    BINDIGIT = "0" | "1".
    OCTDIGIT = "0"..."7".
    HEXDIGIT = "0"..."9" | "A"..."F".
    ESCAPE    = "\a" | "\b" | "\e" | "\f" | "\n" | "\t" | "\v" | "\0" | "\\"
                "\x" HEXDIGIT HEXDIGIT.
    STRCHAR   = " "..."~" except for "\", "'" and '"'.

## Names

    NAME    = LETTER {LETTER | DIGIT}.
    LETTER  = "A"..."Z" | "a"..."z" | "_".
    DIGIT   = "0"..."9".

    ImportedName = ModuleName "::" NAME.
    ModuleName   = NAME.

## Keywords

    Keywords = 
        "break" | "case" | "const" | "default" | "else" | 
        "for" | "if" | "import" | "include" | "interface" |
        "module" | "fn" | "struct" |
        "ref" | "return" | "type" | "let" | "var" | with" | 
        "while".

    StandardDefinitionIds =
        "abs" | "assert" | "bool" | "byte" | "dec" | "exit" | "expect" |
        "false" | "free" | "inc" | "int" | "land" | "len" | 
        "lenint" | "lnot" | "lor" |  "lxor" | "main" | "maxint" | "maxword" | "minint" |
        "new" | "null" | "float" | "sha" | "shl" | "shr" | "true" | "word" | "SYSTEM" |
        "ADDRESS" | "GET" | "MOVE" | "PUT" | "LOC" | "SIZE" | "TYPE" | "TYPESIZE".

Keywords and the names of standard declarations may not be used for any other purpose. 

## Whitespace and comments

    WHITESPACE = SPACER {SPACER}.
    SPACER     = COMMENT | " " | CR | LF | TAB.
    COMMENT    = "//" {" "..."~" | TAB} (CR | LF).

Adjacent names and keywords must be separated by whitespace. Whitespace is allowed anywhere except inside lexical elements (syntactic elements between double quotes and elements with all-uppercase names). Comments begin with `//` and end at the end of the line. Comments are allowed anywhere that whitespace is allowed.

## Source files

    SourceFile = (Interface | Module) {Interface | Module}.

A Vanilla source file contains one or more interfaces or modules. The names of the files are not significant, but the file extension `.van` should be used by convention.



# The Vanilla Syntax

The syntax of Vanilla is presented informally in this document, but is LR(1). [vanilla.mly](vanilla.mly) is an LR(1) skeleton grammar for Ocaml [Menhir](https://gallium.inria.fr/~fpottier/menhir/). [vanilla.lark](vanilla.lark) is an Earley grammar for Python [Lark](https://github.com/lark-parser/lark).   

## The syntax metalanguage

The following is an informal description of the metalanguage used to describe the syntax of Vanilla in this document. It is Nicolas Wirth's ENBF with some extensions:


| Rule example       | Meaning                                         |
|--------------------|-------------------------------------------------|
| Name               | (mixed-case) The name of a grammar rule.                     |
| NAME               | (uppercase) The name of a lexical element's rule. |
| "text"  '@'  "#"   | Lexical elements. E.g. keywords or punctuation symbols |
| CR LF TAB          | The names of special characters.                |
| Name = *x*.        | A grammar rule definition.                      |
| *x* *y*            | *x* followed by *y*                             |
| *x* \| *y*         | Either *x* or *y* is allowed here               |
| [ *x* ]            | An optional *x*                                 |    
| { *x* }            | An optional repetition of *x*                   |    
| *x* ","...         | a non-empty list of *x* separated by literal ","|
| "a"..."z"          | a character between "a" and "z"                 |
| ( *x* )            | parentheses for metasyntax rules                |    

Whitespace is allowed between grammar rule elements. Whitespace is *required* between alphanumeric elements. E.g. there must be whitespace between `var` and a variable name. The lexical rule `WHITESPACE` defines what whitespace is. Whitespace is *not* allowed between the characters of a lexical element. E.g. this is not a Vanilla variable name: `Endian Reversal`.  `CR`, `LF` and `TAB` are examples of special character names.

This is the metasyntax written in itself: 

    Grammar     = Rule {Rule}.
    Rule        = (GRAMRULE | LEXRULE) "=" [Options] ".".
    Options     = Sequence "|"... .
    Sequence    = {Group} | Group [KEYWORD "..."].
    Group       = Element | "{" Options "}" | "[" Options "]" | "(" Options ")".
    Element     = GRAMRULE | LEXRULE | KEYWORD | KEYWORD "..." KEYWORD.

    KEYWORD     = '"' DQCHAR {DQCHAR} '"' | "'" SQCHAR {SQCHAR} "'".
    LEXRULE     = UPPER {UPPER}.
    GRAMRULE    = {UPPER | LOWER} LOWER {UPPER | LOWER}.
    WHITESPACE  = SPACE {SPACE}.

    UPPER       = "A"..."Z"
    LOWER       = "a"..."z"
    DQCHAR      = " "..."&" | "("..."~".
    SQCHAR      = " " | "!" | "#"..."~".
    SPACE       = " " | CR | LF | TAB.
