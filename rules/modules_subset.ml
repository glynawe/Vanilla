(* A subset of Vanilla's module system and top-level defs. *)


(*
Note: the following is abstract in the sense that it does not explicitly 
describe any scheme for separate compilation of modules.
*)
module type ANY = sig
  type t
end

module type EQUALITY = sig
  include ANY
  val equal : t -> t -> bool
end

module type COMPARABLE = sig
  include EQUALITY
  val compare : t -> t -> int
end

module type VALUE = sig  
  include EQUALITY
end


(*
definitions
  - definitions 
  - 'procedure', 'var', 'val' have "type descriptions"
  - 'const' has a "atomic value"
  - 'type' has a type description

  - an opaque type may be given a type definition
    - the opaque type becomes "manifest"
    - an opaque type does not match a manifest type

  declarations
    - a declaration is a definition that has been given "contents" 
      - a procedure is given a "procedure body"
        - it has names for the parameters
        - it has statements to execute
      - a val or var is given an "initial value"
      - an opaque type is given a manifest type
    - a definition may only have one declaration
*)


module type DEFINITION =
sig
  type t
  type type_t
  type value_t
  type body_t

  val make_type : type_t -> t 
  val make_const : value_t -> t 
  val make_var : type_t -> t 
  val make_val : type_t -> t
  val set_procedure : type_t -> t

  val set_type : t -> type_t -> t option
  val set_value : t -> body_t -> t option
  val set_body : t -> body_t -> t option
end

(*
  interfaces
    - "interfaces" are maps of names to definitions
    - an interface can "include" another interface
      - all of the included interface's definitions are copied in
    - an interface can "import" another interface
      - all of the included interface's definitions are copied in,
        but renamed. Each name is prefixed with the name of the
        imported interface.
    - an interface can be made to consider two names "equivalent"
        - this is used by functors
*)
module type INTERFACE =
sig
  type t
  type name_t
  type definition_t
end
(*
  modules
    - a module is an interface that is "complete"
      - all procedures and val descriptions must have declarations
      - all types defined in the module must have been made manifest
      - all 'procedure' descriptions must have declarations
      - 'var' descriptions without declarations will be given default values
    
    - a module has a "public interface"
      - only definitions in the public interface be imported or included
      - the default interface is all definitions without imported names
      - a "public interface" is the name of another interface
          - the public interface is included into the module
          - the module's interface becomes a copy of the public interface

  functors
    - a functor is a module definition with "module parameters"
    - each module parameter has a name and public interface
    - the functor acts as if modules with that name an interface have been imported
    - names from the parameter and functor modules may be declared "equivalent"
      - equivalent names are treated as if they were the same name
        - in the module interfaces
        - in the functor module

*)


module Type (Name: EQUALITY) (GlobalName: EQUALITY) =
struct
  type t =
  | Integer
  | Nil
  | Ref of t
  | Array of int * t
  | Opaque of GlobalName.t
  | Record of (Name.t * t) list

  let rec equal (a: t) (b: t) : bool = 
    match a, b with
    | Integer, Integer -> true
    | Nil, Nil -> true
    | Ref ta, Ref tb -> equal ta tb
    | Array (la, ta), Array (lb, tb) -> la = lb && equal ta tb
    | Opaque na, Opaque nb -> GlobalName.equal na nb
    | Record ra, Record rb -> List.for_all2 equal_elements ra rb 
    | _, _ -> false
  and equal_elements (na, ta) (nb, tb) =
    Name.equal na nb && equal ta tb
end


module Value =
struct 
  type t =
  | Integer of int
  | Nil
  (* etc *)

  let value_equal (a: t) (b: t) : bool =
    match a, b with
    | Integer a', Integer b' -> a' = b'
    | Nil, Nil -> true
    | _, _ -> false
end


module Definition (Name: EQUALITY) (Value: EQUALITY) (Body: ANY) (Type: EQUALITY) =
struct 
  type t =   
  | Type of Type.t
  | Var of Type.t * Value.t option
  | Val of Type.t * Value.t option
  | Const of Type.t * Value.t
  | Procedure of Name.t list * Type.t * Body.t option

  let declared (a: t) : bool =
  match a with
  | Type _
  | Const _
  | Var (_, None)
  | Val (_, None)
  | Procedure (_, _, None) -> false
  | _ -> false

  let equal (a: t) (b: t) : bool =
  match a, b with
  | Type ta, Type tb -> Type.equal ta tb
  | Var (ta, _), Var (tb, _) -> Type.equal ta tb
  | Val (ta, _), Val (tb, _) -> Type.equal ta tb
  | Const (ta, va), Const (tb, vb) -> Type.equal ta tb && Value.equal va vb
  | Procedure (_, ta, _), Procedure (_, tb, _) -> Type.equal ta tb
  | _, _ -> false
end

module Interface (GlobalName: Map.OrderedType) (Definition: EQUALITY) =
struct
  module Contents = Map.Make(GlobalName)
  open Utility.OptionMonad

  type t = Definition.t Contents.t

  let equal (a: t) (b: t) : bool =
    Contents.equal Definition.equal a b

  let add_definition (m: t) (n: GlobalName.t) (d: Definition.t) : t option =
    match Contents.find_opt n m with
    | None -> Some (Contents.add n d m)
    | Some dm when Definition.equal dm d -> Some m
    | Some _ -> None

  let add_interface (m: t) (i: t) : t option =
    fold_option (fun m (n, d) -> add_definition m n d) m (Contents.bindings i)
        
  let contains_definition (m: t) (n: GlobalName.t) (d: Definition.t) : bool =
    match Contents.find_opt n m with
    | Some dm -> Definition.equal dm d
    | None -> false

  let contains_interface (m: t) (i: t) : bool =
    Contents.for_all (contains_definition m) i
end



module Namespace (Name: COMPARABLE) =
struct
  module NameMap = Map.Make(Name)
end


module Equivalent (Name: COMPARABLE) =
struct
  module NameMap = Map.Make(Name)
  type t = Name.t list NameMap.t
  let empty = NameMap.empty
  
  let test (e: t) (a: Name.t) (b: Name.t) : bool =
    Name.equal a b ||
    match NameMap.find_opt a e with
    | Some ns -> List.exists (Name.equal b) ns 
    | None -> false 

  let set (e: t) (a: Name.t) (b: Name.t) : t =
    match NameMap.find_opt a e with
    | Some l ->  
        let e' = NameMap.add a (b :: l) e in
        NameMap.add b (a :: NameMap.find b e) e'
    | None -> 
       NameMap.add a [b] (NameMap.add b [a] e)
end
