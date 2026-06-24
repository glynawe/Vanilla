# Kete

## Syntax

### Constants

    name, x, m

    integer, i
    real, R
    byte, B
    word, W
    string, S

### Environments

    global name, X, T
    | x
    | m :: x

    program, P : m → M

    scope, Σ : x → d

    environment, Γ : {
        local ↦ Σ,         (local scope)
        outer ↦ Γ,         (outer scopes, when in a statement block)
        return ↦ t,        (expected return type, when in a function body)
        program ↦ P,       (modules available to the program)
        modules ↦ m → Γ    (environments of loaded modules)
    }

### Declarations

    module, M
    | module m { ̅I }

    item, I
    | import m;
    | include m;
    | D
    | d

    definition, D
    | V x : t;
    | const x = e;
    | type x = t;
    | fn x f;

    declaration, d
    | V x : t = e;
    | fn x f b
    | Module Γₘ

    variable kind, V
    | var             (mutable)
    | let             (immutable)

    function body, b
    | = e;
    | { ̅s }

### Types

    type, t
    | T
    | τ
    | [] t
    | [i] t
    | ref t
    | struct { ̅F }
    | record r
    | fn f
    | Null
    | Unit
    | Abstract

    numeric type, τ
    | int
    | byte
    | bool
    | word
    | real

    function signature, f
    | (̅p) : t

    parameter, p
    | V x : t

    record signature, r
    | { ̅F }
    | ( T ) { ̅F }

    field, F
    | x : t

### Statements, Expressions

    statement, s
    | V x : t;
    | V x = e;
    | { ̅s }
    | v = e;
    | v o = e;
    | v ( ̅a );
    | ;
    | return;
    | return e;
    | if ( e ) s
    | if ( e ) s₁ else s₂
    | while ( e ) s
    | match ( e ) { ̅c }
    | match ( var d ) { ̅c }

    argument, a
    | e
    | var d

    case, c
    | case ( x : T ) : s
    | default : s
    | null : s

    designator, v
    | X
    | v ^
    | v [ e ]
    | v . X

    expression, e
    | v
    | v ( ̅a )
    | e₀ o e₁
    | - e
    | e₀ && e₁
    | e₀ || e₁
    | ! e
    | null
    | true
    | false
    | i
    | R
    | B
    | W
    | S
    | Z
    | [ ̅e ]      (array)
    | { ̅z }      (structure)

    binary operator, o ∈ {+, -, *, /, %}

    structure field, z
    | x : e

## Rules

<!-- MARK: ENVIRONMENTS
-->

### Environment operators

#### `Γ = ∅, P` global environment for program

    {local ↦ ∅, outer ↦ ∅, return ↦ t, modules ↦ ∅, program ↦ P}
    ————————————————————————————————————————————————————————————
    Γ = ∅, P

#### `Γ' = Γ (x ↦ d)` Γ with x defined as d in the local scope

    Γ' = Γ ⊕ {local ↦ Γ local ⊕ {x ↦ d}}
    ————————————————————————————————————
    Γ' = Γ (x ↦ d)

#### `Γ' = Γ [x ↦ d]` Γ with x defined as d, but only if x is undefined

    x ∉ Dom (Γ local)
    Γ' = Γ (x ↦ d)
    —————————————————
    Γ' = Γ [x]

#### `d = Γ [X]` the definition of X in the environment Γ

    d = Γ local x
    ————————————— in local scope
    d = Γ [x]

    d = (Γ outer) [x]
    ————————————————— in outer scope
    d = Γ [x]

    d = (Γ modules m) [x]
    ————————————————————— in module
    d = Γ [m :: x]

<!-- MARK: MODULES
-->

### Interfaces

#### `̅m ⊢ Γ' = Γ, ̅I` include items into an environment, avoiding include cycles

    m ∉ ̅m
    module m { ̅Iₘ } = Γ program m
    ̅̅m ∪ {m} ⊢ Γ₀ = Γ, ̅Iₘ
    ̅m ⊢ Γ' = Γ₀, ̅I
    ————————————————————————————— include
    ̅m ⊢ Γ' = Γ, include m; ̅I

    Γ' = Γ, I
    ̅m ⊢ Γ' = Γ₀, ̅I
    ——————————————— other
    ̅m ⊢ Γ' = Γ, I ̅I

    ————————————— empty
     ̅m ⊢ Γ = Γ, ∅

### `Γ' = Γ, I` include item into an environment

    m ∉ Dom Γ modules
    module m { ̅Iₘ } = Γ program m
    ∅ ⊢ Γₘ = Γ ⊕ {local ↦ ∅}, ̅Iₘ
    Γ₀ = Γ ⊕ {modules ↦ Γ modules ⊕ {m ↦ Γₘ}}
    Γ' = Γ₀ [m ↦ Module Γₘ]
    ————————————————————————————————————————— import
    Γ' = Γ, import m;

    m ∈ Dom Γ modules
    Γ' = Γ [m ↦ Module (Γ modules m)]
    ————————————————————————————————— reimport
    Γ' = Γ, import m;

    Γ ⊢ D ✓
    Γ' = Γ (name of D ↦ D)
    —————————————————————— definition
    Γ' = Γ, D

    Γ ⊢ (V x : t;) ✓
    Γ' = Γ [x ↦ V x : t = e;]
    ————————————————————————— declare variable
    Γ' = Γ, (V x : t = e;)

    Γ ⊢ (fn x ( ̅p) : t;) ✓
    Γₚ = Γ scope (̅p) : t
    Γₚ ⊢ e ∈ t
    Γ' = Γ (x ↦ fn x (̅p) : t = e;)
    —————————————————————————————— declare expression function
    Γ' = Γ, (fn x (̅p) : t = e;)

    Γ ⊢ (fn x (̅p) : Unit;) ✓
    Γₚ = Γ scope (̅p) : Unit
    Γₚ ⊢ ̅s ✓
    Γ' = Γ (x ↦ fn x (̅p) : Unit { ̅s })
    ——————————————————————————————————————— declare statement function
    Γ' = Γ, (fn x (̅p) { ̅s })

TODO: declarations can replace definitions, definitions can confirm declarations

### `Γ ⊢ D ✓` definition is valid in environment

#### Previously undefined

    x ∉ Dom (Γ local)
    Γ ⊢ t ✓
    —————————————————
    Γ ⊢ (V x : t;) ✓

    x ∉ Dom (Γ local)
    Γ ⊢ t ✓
    ———————————————————
    Γ ⊢ (type x = t;) ✓

    x ∉ Dom (Γ local)
    Γ ⊢ f ✓
    —————————————————
    Γ ⊢ (fn x f;) ✓

    x ∉ Dom (Γ local)
    Γ ⊢ constant e ✓
    ————————————————————
    Γ ⊢ (const x = e;) ✓

#### Redefined

    Γ [x] = V x : t₀;
    Γ ⊢ t ≡ t₀
    —————————————————
    Γ ⊢ (V x : t;) ✓

    Γ [x] = (type x = Abstract;)
    Γ ⊢ t ✓
    ————————————————————————————
    Γ ⊢ (type x = t;) ✓

    Γ [x] = (type x = t₀;)
    Γ ⊢ t ≡ t₀
    ——————————————————————
    Γ ⊢ (type x = t;) ✓

    Γ [x] = fn x f₀;
    Γ ⊢ f ≡ f₀
    ———————————————————
    Γ ⊢ (fn x p : t;) ✓

    Γ [x] = const x = e₀;
    Γ ⊢ constant e = e₀
    —————————————————————
    Γ ⊢ (const x = e₀;) ✓

<!-- MARK: TYPES
-->

### Types

#### `Γ ⊢ t₀ ≡ t₁` types are equivalent

    ————————— same name
    Γ ⊢ T ≡ T

    Γ ⊢ T₀ names t₀
    Γ ⊢ t₀ ≡ t₁
    ——————————————— name on left
    Γ ⊢ T₀ ≡ t₁

    Γ ⊢ T₁ names t₁
    Γ ⊢ t₀ ≡ t₁
    ——————————————— name on right
    Γ ⊢ t₀ ≡ T₁

    τ₀ = τ₁
    ——————————— numeric
    Γ ⊢ τ₀ ≡ τ₁

    Γ ⊢ t₀ ≡ t₁
    ————————————————————— open array
    Γ ⊢ ([] t₀) ≡ ([] t₁)

    i₀ = i₁
    Γ ⊢ t₀ ≡ t₁
    ————————————————————————— array
    Γ ⊢ ([i₀] t₀) ≡ ([i₁] t₁)

    Γ ⊢ t₀ ≡ t₁
    ——————————————————————— pointer
    Γ ⊢ (ref t₀) ≡ (ref t₁)

    Γ ⊢ f₀ ≡ f₁
    ————————————————————— function
    Γ ⊢ (fn f₀) ≡ (fn f₁)

    Γ ⊢ ̅F₀ ≡ ̅F₁
    ————————————————————————————————————— structure
    Γ ⊢ (struct { ̅F₀ }) ≡ (struct { ̅F₁ })

### `Γ ⊢ ̅F₀ ≡ ̅F₁` field lists are equivalent

    x₀ = x₁
    Γ ⊢ t₀ ≡ t₁
    Γ ⊢ ̅F₀ ≡ ̅F₁
    —————————————————————————————————
    Γ ⊢ (x₀: t₀ ; ̅F₀) ≡ (x₁: t₁ ; ̅F₁)

    —————————
    Γ ⊢ ∅ ≡ ∅

#### `Γ ⊢ f₀ ≡ f₁` function signatures are equivalent

    Γ ⊢ ̅p₀ ≡ ̅p₁
    Γ ⊢ t₀ ≡ t₁
    —————————————————————
    Γ ⊢ ̅p₀ : t₀ ≡ ̅p₁ : t₁

#### `Γ ⊢ ̅p₀ ≡ ̅p₁` parameter lists are equivalent

    Γ ⊢ t₀ ≡ t₁
    Γ ⊢ ̅p₀ ≡ ̅p₁
    ——————————————————————————————————— value
    Γ ⊢ ((x₀ : t₀) ̅p₀) ≡ ((x₁ : t₁) ̅p₁)

    Γ ⊢ t₀ ≡ t₁
    Γ ⊢ ̅p₀ ≡ ̅p₁
    ——————————————————————————————————————————— variable
    Γ ⊢ ((var x₀ : t₀) ̅p₀) ≡ ((var x₁ : t₁) ̅p₁)

    —————————
    Γ ⊢ ∅ ≡ ∅

### `Γ ⊢ t₀ ⊆ t₁` types are equivalent, or record extension

    t₀ ≡ t₁
    —————————————————
    Γ ⊢ t₀ ⊆ t₁

    Γ ⊢ T₀ is record T' { ̅F₀ }
    Γ ⊢ T₁ names t₁
    Γ ⊢ t₁ is record r
    Γ ⊢ T' ⊆ t₁
    ——————————————————————————
    Γ ⊢ T₀ ⊆ T₁

#### `Γ ⊢ t₀ assignable to t₁` types are assignment compatible

    Γ ⊢ t₀ ⊆ t₁
    ———————————————————————
    Γ ⊢ t₀ assignable to t₁

    —————————————————————————————— null pointer
    Γ ⊢ Null assignable to (ref t)

    Γ ⊢ t₀ is [i₀] t₂
    Γ ⊢ t₁ is [i₁] t₃
    Γ ⊢ t₂ assignable to t₃
    i₀ ≤ i₁
    ——————————————————————— arrays
    Γ ⊢ t₀ assignable to t₁

    Γ ⊢ t₀ is [] t₂
    Γ ⊢ t₁ is [] t₃ ∨ Γ ⊢ t₁ is [i] t₃
    Γ ⊢ t₂ assignable to t₃
    —————————————————————————————————— open array left
    Γ ⊢ t₀ assignable to t₁

    Γ ⊢ t₀ is [i] t₂ ∨ Γ ⊢ t₁ is [] t₂
    Γ ⊢ t₁ is [] t₃
    Γ ⊢ t₂ assignable to t₃
    —————————————————————————————————— open array right
    Γ ⊢ t₀ assignable to t₁

#### `Γ ⊢ t₀ is t₁` t₀ is structurally equal to t₁

    Γ [T₀] = (type x = t₀;)
    Γ ⊢ t₀ is t₁
    ———————————————————————
    Γ ⊢ T₀ is t₁

    Γ ⊢ ̅F₀ ≡ ̅F₁
    ——————————————————————————————————
    Γ ⊢ record { ̅F₀ } is record { ̅F₁ }

    Γ ⊢ T₀ ≡ T₁
    Γ ⊢ ̅F₀ ≡ ̅F₁
    ————————————————————————————————————————
    Γ ⊢ record T₀ { ̅F₀ } is record T₁ { ̅F₁ }

    ————————————————————————
    Γ ⊢ Abstract is Abstract

    ————————————————
    Γ ⊢ Unit is Unit

    ————————————————
    Γ ⊢ Null is Null

    Γ ⊢ t₀ ≡ t₁
    ————————————
    Γ ⊢ t₀ is t₁

#### `Γ ⊢ T names t` dereference type names

    Γ [T] = (type x = Abstract;)
    ———————————————————————————— name of abstract type
    Γ ⊢ T names T

    Γ [T] = (type x = record r;)
    ———————————————————————————— name of record
    Γ ⊢ T names T

    Γ [T] = (type x = T';)
    Γ ⊢ T' names t
    —————————————————————— renames a name
    Γ ⊢ T names t

    Γ [T] = (type x = t;)
    —————————————————————
    Γ ⊢ T names t

### `Γ ⊢ t ✓` type is valid

    Γ [T] = type x = t;
    Γ ⊢ t ✓
    ———————————————————
    Γ ⊢ T ✓

    ———————
    Γ ⊢ τ ✓

    Γ ⊢ t ✓ storable
    i > 0
    ————————————————
    Γ ⊢ [i] t ✓

    Γ ⊢ ̅F ✓
    ——————————————————
    Γ ⊢ struct { ̅F } ✓

    Γ ⊢ ̅F ✓
    ——————————————————
    Γ ⊢ record { ̅F } ✓

    ̅Fₚ = fields T
    Γ ⊢ Fₚ ; ̅F ✓
    ————————————————————
    Γ ⊢ record T { ̅F } ✓

    Γ ⊢ f ✓
    ——————————
    Γ ⊢ fn f ✓

### `Γ ⊢ t ✓ returnable`

    Γ ⊢ t ✓
    ¬ t is [] t₀
    ¬ t is Null
    ¬ t is Abstract
    ————————————————
    Γ ⊢ t ✓ storable

### `Γ ⊢ t ✓ storable`

    Γ ⊢ t ✓ returnable
    ¬ t is Unit
    ——————————————————
    Γ ⊢ t ✓ storable

### `Γ ⊢ ̅F ✓` field list is valid

    distinct names ̅F
    ∀(x : t) ∈ ̅F: Γ ⊢ t ✓ storable
    ——————————————————————————————
    Γ ⊢ ̅F ✓

### `Γ ⊢ f ✓` function signature is valid

    Γ ⊢ ̅p ✓
    Γ ⊢ t ✓ returnable
    ——————————————————
    Γ ⊢ (̅p) : t ✓

### `Γ ⊢ ̅p ✓` function parameters are valid

    distinct names ̅p
    ∀(V x : t) ∈ ̅p: Γ ⊢ t ✓
    ———————————————————————
    Γ ⊢ ̅p ✓

<!-- MARK: STATEMENTS
-->

### Statements

#### `Γₚ = Γ scope f` procedure scope

    Γ ⊢ (̅p) : t ✓
    Γ₀ = Γ ⊕ {local ↦ ∅, outer ↦ Γ, return ↦ t}
    Γₚ = Γ₀, ̅p
    ———————————————————————————————————————————
    Γₚ = Γ scope (̅p) : t

#### `Γ' = Γ, ̅p`

    Γ ⊢ t ✓
    Γ₀ = Γ [x ↦ V x : t]
    Γ' = Γ₀, ̅p
    ————————————————————
    Γ' = Γ, (V x : t) ̅p

    ————————
    Γ = Γ, ∅

#### `Γ' = Γ, s` environment updated by a valid statement

    Γ₀ = Γ ⊕ {local ↦ ∅, outer ↦ Γ}
    Γ' = Γ₀, ̅s
    ——————————————————————————————— block
    Γ = Γ, ({ ̅s })

    x ∉ Dom (Γ local)
    Γ ⊢ t ✓ storable
    Γ ⊢ e ∈ tₑ
    Γ ⊢ tₑ assignable to t
    Γ' = Γ [x ↦ V x : t]
    —————————————————————— variable
    Γ' = Γ, (V x : t = e;)

    Γ ⊢ e = default t
    Γ' = Γ, (V x : t = e;)
    —————————————————————— variable, implicit initializer
    Γ' = Γ, (V x : t;)

    Γ ⊢ e ∈ t
    Γ' = Γ, (V x : t = e;)
    —————————————————————————— variable, implicit type
    Γ' = Γ, (V x = e;)

    Γ return = Unit
    ———————————————— return
    Γ = Γ, (return;)

    t = Γ return
    Γ ⊢ e ∈ tₑ
    Γ ⊢ tₑ assignable to t
    —————————————————————— return expression
    Γ = Γ, (return e;)

    Γ ⊢ v ∈ tᵥ
    Γ ⊢ e ∈ tₑ
    Γ ⊢ tₑ assignable to tᵥ
    ——————————————————————— assignment
    Γ = Γ, (v = e;)

    Γ = Γ, (v = v o e;)
    —————————————————— operator assignment (e.g. +=)
    Γ = Γ, (v o = e)

    Γ ⊢ v ∈ fn ((̅p) : Unit)
    ∀ a p ∈ zip ̅a ̅p: Γ ⊢ a matches p
    ———————————————————————————————— call
    Γ = Γ, (v ( ̅a );)

    —————————— empty
    Γ = Γ, (;)

    Γ ⊢ e ∈ bool
    Γ' = Γ, s
    —————————————————————— while
    Γ = Γ, (while ( e ) s)

    Γ ⊢ e ∈ bool
    Γ' = Γ, s
    ——————————————————— if then
    Γ = Γ, (if ( e ) s)

    Γ ⊢ e ∈ bool
    Γ₀ = Γ, s₀
    Γ₁ = Γ, s₁
    ———————————————————————————— if then else
    Γ = Γ, (if ( e ) s₀ else s₁)

    Γ ⊢ e ∈ t
    Γ ⊢ t is record
    TODO:
    —————————————————————————— record expression subtype match
    Γ = Γ, (match ( e ) { ̅c })

    Γ ⊢ e ∈ t
    Γ ⊢ t is record
    TODO:
    —————————————————————————————— record variable subtype match
    Γ = Γ, (match ( var d ) { ̅c })

#### `Γ' = Γ, ̅s` environment updated by a valid statement list

    Γ₀ = Γ,  s
    Γ' = Γ₀, ̅s
    ———————————
    Γ' = Γ, s ̅s

    ————————
    Γ = Γ, ∅

<!-- MARK: EXPRESSIONS
-->

### Expressions

#### `Γ ⊢ e ∈ t` type of an expression

    Γ ⊢ v ∈ V t
    ——————————— designator
    Γ ⊢ v ∈ t

    Γ ⊢ v ∈ V (fn (̅p) : t)
    ∀ a p ∈ zip ̅a ̅p: Γ ⊢ a matches p
    ———————————————————————————————— function call
    Γ ⊢ (v (̅a)) ∈ t

    Γ ⊢ e₀ ∈ τ
    Γ ⊢ e₁ ∈ τ
    ————————————————— binary operator
    Γ ⊢ (e₀ o e₁) ∈ τ

    Γ ⊢ e₀ ∈ bool
    Γ ⊢ e₁ ∈ bool
    ————————————————————— or
    Γ ⊢ (e₀ || e₁) ∈ bool

    Γ ⊢ e₀ ∈ bool
    Γ ⊢ e₁ ∈ bool
    ————————————————————— and
    Γ ⊢ (e₀ && e₁) ∈ bool

    Γ ⊢ e ∈ τ
    ———————————— negate
    Γ ⊢ (-e) ∈ τ

    Γ ⊢ e ∈ bool
    ——————————————— not
    Γ ⊢ (!e) ∈ bool

    ——————————————————————————— string constant
    Γ ⊢ S ∈ [length S + 1] byte

    ∀e ∈ ̅e: Γ ⊢ e ∈ t
    i = length ̅e
    ————————————————— array constant
    Γ ⊢ [ ̅e ] ∈ [i] t

    Γ ⊢ e ∈ t
    Γ ⊢ { ̅z } ∈ struct { ̅F }
    ———————————————————————————————————— structure constant
    Γ ⊢ { x: e; ̅z } ∈ struct { x: t; ̅F }

    ————————————————————————
    Γ ⊢ { ∅ } ∈ struct { ∅ }

    ———————————
    Γ ⊢ i ∈ int

    ————————————
    Γ ⊢ B ∈ byte

    ————————————
    Γ ⊢ W ∈ word

    ————————————
    Γ ⊢ R ∈ real

    ————————————————
    Γ ⊢ false ∈ bool

    ———————————————
    Γ ⊢ true ∈ bool

    ———————————————
    Γ ⊢ null ∈ Null

#### `Γ ⊢ a matches p` function argument matches parameter

    Γ ⊢ a ∈ V tₐ
    Γ ⊢ tₐ assignable to t
    —————————————————————————
    Γ ⊢ a matches (x : t)

    Γ ⊢ a ∈ var tₐ
    Γ ⊢ tₐ assignable to t
    —————————————————————————
    Γ ⊢ a matches (var x : t)

<!-- MARK: DESIGNATORS
-->

### Designators

#### `Γ ⊢ d ∈ V t` type and mutability of a designator

    Γ [X] = V t
    ——————————— variable
    Γ ⊢ X ∈ V t

    Γ [X] = (const x = e;)
    Γ ⊢ e ∈ t
    ————————————————————— constant
    Γ ⊢ X ∈ Constant t

    Γ [X] = (fn x f b)
    —————————————————— function
    Γ ⊢ X ∈ let fn f

    Γ ⊢ e ∈ int
    Γ ⊢ v ∈ V ([a] t)
    ——————————————————— array subscript
    Γ ⊢ (v [ e ]) ∈ V t

    Γ ⊢ e ∈ int
    Γ ⊢ v ∈ V ([] t)
    ——————————————————— open array subscript
    Γ ⊢ (v [ e ]) ∈ V t

    Γ ⊢ e ∈ int
    Γ ⊢ v ∈ V (ref t)
    ——————————————————— pointer dereference
    Γ ⊢ (v [ e ]) ∈ V t

    Γ ⊢ v ∈ V (struct ̅F)
    (x : t) ∈ ̅F
    ———————————————————— struct field selection
    Γ ⊢ (v . x) ∈ V t

    Γ ⊢ v ∈ V T
    Γ ⊢ ̅F = fields T
    (x : t) ∈ ̅F
    ————————————————— record field selection
    Γ ⊢ (v . x) ∈ V t

### `Γ ⊢ ̅F = fields T` the fields of record T

    Γ ⊢ T is record { ̅F };
    ——————————————————————
    Γ ⊢ ̅F = fields T

    Γ ⊢ T is record (Tₚ) { ̅F₀ };
    Γ ⊢ ̅Fₚ = fields Tₚ
    ̅F = ̅Fₚ; ̅F
    ———————————————————————————
    Γ ⊢ ̅F = fields T

<!-- MARK: (FOOTNOTES)
-->

## (Footnotes)

### Notation

An overbar over a syntactic variable means that it represents a list of
those variables. Most set operators are valid for lists, lists are
"bags". `∅` represents an empty list. Sequences can be shown with
separators between elements (e.g. `,` or `;`), but those have no significance.

Sequences can be:

- destructured, `̅α = α₀ ̅α₀`;
- concatenated, `α ̅α` or `̅α₀ ̅α₁`;
- constructed,  `[α₀ α₁ ... αₙ]` or `[f(α) | α ∈ ̅α]`;
- quantified,   `∀α ∈ ̅α: f(α)`;
- searched,     `α ∈ ̅α`;
- dereferenced  `α = ̅α i`.

## TODO: (Undefined Rules)

`P ⊢ M defines Γ` module, environment

`Γ' = Γ, D` module item, updated environment

`Γ ⊢ d ✓` declaration is valid

`Γ ⊢ t ✓` type is valid

`Γ ⊢ e constant` expression is constant

`Γ ⊢ Z ∈ t` type of a structure expression

`x = name of D` the name part of a definition

`Γ ⊢ e = default t` the default value for a type

- Pointer, record and function types: `null`;
- numeric types: the zero for that type;
- non-open arrays: the element type's default value in each element;
- structs, the default value for each field in each field;
- invalid for all other types.

