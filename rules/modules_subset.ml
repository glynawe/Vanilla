(* A subset of Vanilla's module system and top-level definitions. *)

module type PROGRAM = 
sig
  type t
  type name_t
  type module_t
  val get : t -> name_t -> module_t option
end


module type MODULE = 
sig
  type t
  type type_t
  type name_t
  type globalname_t
  type definition_t

  val get : t -> globalname_t -> definition_t option

  (* Get the type of a definition. *) 
  (* None if the name is not defined or not a type. *) 
  val get_type : t -> globalname_t -> type_t option

  (* True if two type definitions are equivalent. *)
  (* Either if the names are the same, or are names defined as
     equivalent by a functor declaration. *)
  val equivalent : t -> globalname_t -> globalname_t -> bool
end


module type DEFINITION = 
sig
  type name_t
  type type_t
  type value_t

  type t =
  | Type of type_t
  | Var of type_t
  | Val of type_t * value_t option
  | Const of type_t * value_t
  | Procedure of name_t list * type_t
end


module type NAME = 
sig
  type t
  val equal : t -> t -> bool
  val compare : t -> t -> int 
end


module type GLOBALNAME = 
sig
  type name_t

  type t =
  | Local of name_t
  | Imported of name_t * name_t

  val equal : t -> t -> bool
  val compare : t -> t -> int 
end
