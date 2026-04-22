# Syntax 

    N, M : name

    i : integer

    global name, V, T, R
    | N
    | M::N 

    program, P : M → ̅D

    declaration, D
    | include N
    | import N
    | type N = t
    | const N = x
    | val N : t
    | val N : t = x
    | var N : t
    | fn N f
    | fn N f { ̅s }

    statement, s
    | v := x;
    | ...

    expression, x
    | i
    | v
    | v ( ̅a )
    | v -> N ( ̅a )
    | ...

    argument, a
    | x
    | var v 

    designator, v
    | V
    | v^
    | v[x]
    | v.N

    env, E : N → d

    definition, d  
    | Type t
    | Const x
    | Var t
    | Val t
    | Val t = x
    | Fn f
    | Fn f B

    type, t
    | T
    | int
    | byte
    | word
    | real
    | [n] t
    | [] t
    | ref t
    | fn f
    | struct { ̅e }
    | record r
    | nulltype
    | abstract
    | statement

    record, r
    | { ̅e }
    | R { ̅e }

    field, e
    | N : t

    function, f
    | ( ̅p )  : t

    parameter, p  
    | N : t
    | var N : t




## Notation

An overbar over a variable name means that it is a sequence of those variables
separated by semicolons or commas. `∅` is the empty sequence. These sequences can be destructured: `̅e = e₀ ; ̅e₀` or concatenated: `e ; ̅e`, `̅e = ̅e₀ ; ̅e₁`. `zip` pairs the elements of two sequences, if they are the same length. `∀` and `∃` may be used on sequences.


# Declarations


## `P, E ⊢ D ⟹ E'`   make a declaration

### import, include

    M ∈ Dom P
    P, E ⊢ P(M) ⟹ E'
    ———————————————————————— include
    P, E ⊢ (include M) ⟹ E'


    M ∈ Dom P
    P, ∅ ⊢ P(M) ⟹ E₀
    E' = X ⊕ {M::N ↦ d | (N ↦ d) ∈ E₀}
    —————————————————————————————————— import
    P, E ⊢ (import M) ⟹ E'


### type

    N ∉ Dom E
    E ⊢ t ✓ declarable
    ———————————————————————————————————— new type
    E ⊢ (type N = t) ⟹ E ∪ {N ↦ Type t}


    N ∉ Dom E 
    ——————————————————————————————————————— new abstract type
    E ⊢ (type N) ⟹ E ∪ {N ↦ Type abstract}


    E ⊢ E(N) ≡ Type abstract
    E ⊢ t ✓ declarable
    ———————————————————————————————————— abstract type made concrete
    E ⊢ (type N = t) ⟹ E ⊕ {N ↦ Type t}


    E ⊢ E(N) ≡ Type t
    ———————————————————————— redundant type declaration
    E ⊢ (type N = t) ⟹ E


    E ⊢ E(N) ≡ Type abstract 
    ———————————————————————— redundant abstract type declaration
    E ⊢ (type N) ⟹ E


### var

    N ∉ Dom E
    E ⊢ t ✓ assignable
    ——————————————————————————————————— new var 
    E ⊢ (var N : t) ⟹ E  ∪ {N ↦ Var t}


    E ⊢ E(N) ≡ Var t
    ———————————————————— redundant var declaration
    E ⊢ (var N : t) ⟹ E


### val

Note: a `val` cannot be given more than one assignment.

    N ∉ Dom E
    E ⊢ t ✓ assignable
    ——————————————————————————————————— new val
    E ⊢ (var N : t) ⟹ E  ∪ {N ↦ Val t}


    N ∉ Dom E
    E ⊢ t ✓ assignable
    E ⊢ t = typeof x
    —————————————————————————————————————————— new assigned val
    E ⊢ (var N : t = x) ⟹ E ∪ {N ↦ Val t = x}


    E ⊢ E(N) ≡ Val t
    E ⊢ t ✓
    —————————————————————————————————————————— existing val assigned 
    E ⊢ (var N : t = x) ⟹ E ⊕ {N ↦ Val t = x}


    E ⊢ E(N) ≡ Val t
    ———————————————————— redundant val declaration
    E ⊢ (val N : t) ⟹ E


## fn


    N ∉ Dom E
    E ⊢ t ✓ assignable
    E ⊢ t = typeof x
    ———————————————————————————— new function prototype
    E ⊢ (fn f) ⟹ E ∪ {N ↦ Fn f}


    N ∉ Dom E
    E ⊢ t ✓ assignable
    E ⊢ t = typeof B
    E ⊢ 
    —————————————————————————————— new function
    E ⊢ (fn f) ⟹ E ∪ {N ↦ Fn f B}


    E ⊢ E(N) ≡ Val t
    N ∈ Dom E
    E 
    E ⊢ t ✓ assignable
    E ⊢ t = typeof x
    ———————————————————————————— new function prototype
    E ⊢ (fn f) ⟹ E ∪ {N ↦ Fn f}


## `P, E ⊢ ̅D ⟹ E'`   make a sequence of declarations   

    M ∈ Dom P
    P, E ⊢ D ⟹ E₀
    P, E₀ ⊢ ̅D ⟹ E'
    —————————————————— sequence of declarations
    P, E ⊢ D; ̅D ⟹ E'


    ————————————— empty sequence
    P, E ⊢ ∅ ⟹ E



# Equivalences

## `E ⊢ d₀ ≡ d₁`  equivalent declarations 


    E ⊢ t₀ ≡ t₁
    ————————————————— type
    Type t₀ ≡ Type t₁ 


    E ⊢ t₀ ≡ t₁
    ——————————————— var
    Var t₀ ≡ Var t₁ 


    E ⊢ t₀ ≡ t₁
    ——————————————— unassigned val
    Val t₀ ≡ Val t₁ 


    E ⊢ e₀ = x₁
    ——————————————————— constant
    Const e₀ ≡ Const e₁ 



## `E ⊢ t₀ ≡ t₁`  equivalent types


Note: abstract and record types can only be equivalent by name.


    E ⊢ t₁ ≡ t₀
    ——————————— symmetric
    E ⊢ t₀ ≡ t₁         


    T₀ = T₁
    ——————————— same name
    E ⊢ T₀ ≡ T₁


    E(T) = Type t₀
    E ⊢ t₀ ≡ t
    —————————————— name
    E ⊢ T ≡ t


    E ⊢ t₀ ≡ t₁
    ————————————————— open arrays
    E ⊢ [] t₀ ≡ [] t₁


    E ⊢ n₀ = valueof x₀
    E ⊢ n₁ = valueof x₁
    n₀ = n₁
    E ⊢ t₀ ≡ t₁
    ——————————————————— arrays
    E ⊢ [x] t₀ ≡ [x] t₁


    E ⊢ t₀ ≡ t₁
    —————————————————— arrays and open arrays 
    E ⊢ [] t₀ ≡ [x] t₁


    E ⊢ t₀ ≡ t₁
    ——————————————————— pointers
    E ⊢ ref t₀ ≡ ref t₁


    E ⊢ ̅F₀ ≡ ̅F₀
    ——————————————————————————————— structures
    E ⊢ struct { ̅F₀} ≡ struct { ̅F₀}


    E ⊢ t₀ ≡ t₁
    E ⊢ ̅p₀ ≡ ̅p₁
    ————————————————————————————————— functions
    E ⊢ fn ( ̅p₀) : t₀ ≡ fn ( ̅p₁) : t₁


    t₀ ∈ {int, byte, word, real, nulltype, statement}
    t₁ ∈ {int, byte, word, real, nulltype, statement}
    t₀ = t₁
    ————————————————————————————————————————————————— basic types
    E ⊢ t₀ ≡ t₁



## `E ⊢ ̅p₀ ≡ ̅p₁`  equivalent function parameter lists

    Note: parameter names are deliberately ignored.


    E ⊢ t₀ ≡ t₁
    E ⊢ ̅p₀ ≡ ̅p₁
    ——————————————————————————————— value parameter pairs
    E ⊢ N₀ : t₀; ̅p₀ ≡ N₁ : t₁; ̅p₁


    E ⊢ t₀ ≡ t₁
    E ⊢ ̅p₀ ≡ ̅p₁
    ——————————————————————————————————————— reference parameter pairs
    E ⊢ var N₀ : t₀; ̅p₀ ≡ var N₁ : t₁; ̅p₁


    ————————— empty list
    E ⊢ ∅ ≡ ∅



## `E ⊢ ̅F₀ ≡ ̅F₁`  equivalent structure field lists


    E ⊢ t₀ ✓ storable
    E ⊢ t₁ ✓ storable
    E ⊢ t₀ ≡ t₁
    E ⊢ ̅F₀ ≡ ̅F₁
    ——————————————————————————————— pairs
    E ⊢ N₀ : t₀; ̅e₀ ≡ N₁ : t₁; ̅e₁


    ————————— empty list
    E ⊢ ∅ ≡ ∅


# Validity


## `E ⊢ t ✓`  type is valid         


    t ∈ {int, byte, word, real, nulltype, abstract, statement}
    —————————————————————————————————————————————————————————— simple
    E ⊢ t ✓


    E ⊢ t ✓ storable
    E ⊢ n = valueof x
    n > 0
    ————————————————— array
    E ⊢ [x] t ✓


    E ⊢ t ✓ storable
    ———————————————— open array
    E ⊢ [] t ✓


    E ⊢ t ✓ assignable
    —————————————————— pointer
    E ⊢ ref t ✓


    ∀p ∈ ̅p: E ⊢ p ✓
    distinct names ̅p 
    E ⊢ t ✓ returnable
    —————————————————— function
    E ⊢ fn ( ̅p) : t ✓


    ∀(X : t) ∈ ̅e: E ⊢ t ✓ storable
    distinct names ̅e 
    ——————————————————————————————— structure
    E ⊢ struct { ̅e } ✓


    E ⊢ struct { ̅e } ✓ 
    distinct names ̅e 
    ——————————————————— base record
    E ⊢ record { ̅e } ✓


    E ⊢ R ≡ Type record { ̅e₀ }
    E ⊢ ̅e₀ = fieldsof R₀
    E ⊢ struct { ̅e₀ ; ̅e } ✓ 
    ——————————————————————————— record extended with base record
    E ⊢ record (R) { ̅e } ✓


    E ⊢ R ≡ Type record R₀ { ̅e₀ }
    E ⊢ R₀ ✓
    E ⊢ ̅e₀ = fieldsof R₀
    E ⊢ struct { ̅e₀ ; ̅e } ✓ 
    —————————————————————————————— record extended with extended record
    E ⊢ record (R) { ̅e } ✓


## Type properties

### `E ⊢ t ✓ declarable` type can be declared 

    E ⊢ t ✓
    ¬ E ⊢ t = nulltype
    ¬ E ⊢ t = abstract
    ¬ E ⊢ t = statement
    ———————————————————
    E ⊢ t ✓ declarable


### `E ⊢ t ✓ assignable` type can be assigned to a variable


    E ⊢ t ✓ declarable
    ———————————————————
    E ⊢ t ✓ assignable


### `E ⊢ t ✓ storable` type can be stored in RAM (has a fixed size)


    E ⊢ t ✓ assignable
    ¬ E ⊢ t = [] t₀
    ———————————————————
    E ⊢ t ✓ storable


### `E ⊢ t ✓ returnable` type can be returned from a function

    E ⊢ t ✓ assignable
    ———————————————————
    E ⊢ t ✓ returnable

    t = statement
    ———————————————————
    E ⊢ t ✓ returnable



## `E ⊢ p ✓`  function parameter is valid


    E ⊢ t ✓ assignable
    ——————————————————
    E ⊢ N : t ✓ 


    E ⊢ t ✓ assignable
    ——————————————————
    E ⊢ var N : t ✓ 



# Properties

## `E ⊢ ̅e = fieldsof R`  record has a list of fields


    E ⊢ R ≡ Type record { ̅e }
    ——————————————————————————
    E ⊢ ̅e = fieldsof R


    E ⊢ R ≡ Type record (R₁) { ̅e₀ }
    E ⊢ ̅e₁ = fieldsof R₁
    ———————————————————————————————
    E ⊢ ( ̅e₀ ; ̅e₁) = fieldsof R



## `E ⊢ typeof B ≡ t`  the return type of function body `B` is equivalent to `t`


    E ⊢ typeof x ≡ t
    ———————————————— expression
    E ⊢ (= x) ≡ t


    XXX
    ———————————————— statement block
    E ⊢ { ̅s } ≡ t



## `E ⊢ typeof v ≡ t`  the type of variable `v` is equivalent to `t`


    E(V) = Var t'
    E ⊢ t ≡ t'
    ———————————————— variable name
    E ⊢ typeof V ≡ t


    E ⊢ typeof v ≡ ref t₀
    E ⊢ t ≡ t₀
    ————————————————————— dereference
    E ⊢ typeof v^ ≡ t


    E ⊢ typeof v ≡ [e₀] t₀
    E ⊢ t ≡ t₀
    E ⊢ typeof x₀ ≡ int
    —————————————————————— subscript
    E ⊢ typeof v[x] ≡ t


    E ⊢ typeof v ≡ t'
    E ⊢ t ≡ t'.N
    —————————————————— selection
    E ⊢ typeof v.N ≡ t



## `E ⊢ typeof t₀.N ≡ t₁`  the type of field `N` of type `t` is equivalent to `t`


    E ⊢ t₀ ≡ struct { ̅e }
    E ⊢ t₁ ≡ typeof ̅e.N
    ————————————————————— structure
    E ⊢ typeof t₀.N ≡ t₁


    E ⊢ t₀ ≡ record { ̅e }
    E ⊢ t₁ ≡ typeof ̅e.N
    ————————————————————— record
    E ⊢ typeof t₀.N ≡ t₁


    E ⊢ t₀ ≡ record (R) { ̅e }
    E ⊢ t₁ ≡ typeof ̅e.N
    ————————————————————————— extended record, in list
    E ⊢ typeof t₀.N ≡ t₁


    E ⊢ t₀ ≡ record (R) { ̅e }
    E ⊢ typeof R.N ≡ t₁
    ————————————————————————— extended record, in parent
    E ⊢ typeof t₀.N ≡ t₁


    E ⊢ t₀ ≡ ref t'
    E ⊢ typeof t'.N ≡ t₁
    ———————————————————— pointer
    E ⊢ typeof t₀.N ≡ t₁



## `E ⊢ typeof ̅e.N ≡ t`  the type of field `N` is equivalent to `t`


    N₀ = N
    E ⊢ t₀ ≡ t
    —————————————————————————— first
    E ⊢ type (N₀:t₀ ; ̅e).N ≡ t


    N₀ ≠ N
    E ⊢ typeof ̅e.N ≡ t
    —————————————————————————— rest
    E ⊢ type (N₀:t₀ ; ̅e).N ≡ t



## `E ⊢ t₀ assignable t₁`  a variable of type `t₀` can be assigned `t₁` values 


    E ⊢ t₀ ≡ t₁
    ———————————————————— same type
    E ⊢ t₀ assignable t₁


    E ⊢ t₀ ≡ ref t
    E ⊢ t₁ ≡ null
    ———————————————————— null reference
    E ⊢ t₀ assignable t₁


    E ⊢ t₀ ≡ record r
    E ⊢ t₁ ≡ null
    ———————————————————— null record
    E ⊢ t₀ assignable t₁


    E ⊢ t₀ ≡ fn f
    E ⊢ t₁ ≡ null
    ———————————————————— null function
    E ⊢ t₀ assignable t₁


    E ⊢ t₀ ≡ [] t₃
    E ⊢ t₁ ≡ [] t₄
    E ⊢ t₃ ≡ t₄ 
    ———————————————————— open arrays
    E ⊢ t₀ assignable t₁


    E ⊢ t₀ ≡ [] t₃
    E ⊢ t₁ ≡ [x] t₄
    E ⊢ t₃ ≡ t₄ 
    ———————————————————— open array, array
    E ⊢ t₀ assignable t₁


    E ⊢ t₀ ≡ [x] t₃
    E ⊢ t₁ ≡ [] t₄
    E ⊢ t₃ ≡ t₄ 
    ———————————————————— array, open array
    E ⊢ t₀ assignable t₁


# Statements


## `E ⊢ s ✓`  statement is valid


    E ⊢ t₀ ≡ typeof v
    E ⊢ t₁ ≡ typeof x
    E ⊢ t₀ assignable t₁ 
    ———————————————————— assignment
    E ⊢ v := x ✓

    ...

