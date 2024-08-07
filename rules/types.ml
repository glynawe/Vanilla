(* The Vanilla type rules in OCaml. *)

(* ------------------------------------------------------------------------- *)
(* Names and Interfaces *)
(* ------------------------------------------------------------------------- *)

module type NAME = 
sig
  type t
  val equal : t -> t -> bool
end

(* Opaque types and some record types need to be tested for equality by 
   name rather than their structure. That means the type system needs 
   a "Interface.get_type" function to look up interfaces for type definitions.
   
   Functors can declare that two names refer to the same type by
   type constraint. The "Interface.equivalent" function is aware of this.
   See https://github.com/glynawe/Vanilla/blob/master/vanilla.md#modules-and-interfaces *) 

module type INTERFACE = 
sig
  type t
  type type_t
  type globalname_t

  val equivalent : t -> globalname_t -> globalname_t -> bool
  val get_type : t -> globalname_t -> type_t option
end


(* ------------------------------------------------------------------------- *)
(* Types *)
(* ------------------------------------------------------------------------- *)

  (* Vanilla has "opaque types" whose definitions are hidden in other 
  modules or are unknown because they are in the parameters of a functor.
  Because the size of opaque types are unknown they may only be used as
  the targets of reference types or as pass-by-reference parameters.

  References to named types also allow records to refer to themselves
  recursively. Eg. "type List = record I: integer; R: ref List end".
  Type checking does not examine the contents of a named referenced 
  type if it is a record or opaque. 
  
  "Nil" is the type of the "nil" constant, which can be assigned to any 
  reference variable. It can only be used as the type of an expression.
  "Statement" is the return type for proper procedures, which do not return 
  values. It can only be used for that purpose. *)

module type TYPE =
sig
  type name_t
  type globalname_t

  type t =
      Statement
    | Integer
    | Byte
    | Word
    | Real
    | Boolean
    | Ref of t
    | NamedRef of globalname_t
    | Nil
    | Array of int * t
    | OpenArray of t
    | Record of element_t list
    | Opaque of globalname_t
    | Procedure of parameter_t list * t
  and parameter_t = 
    passing_method_t * t
  and passing_method_t = 
      ByReference 
    | ByValue
  and element_t = 
    name_t * t

  (* I only mean to describe Vanilla's semantics at the module level. Procedure
     calls are at the statement and expression level, but procedure calls are an
     aspect of procedure types, so it might be wise to include a description of
     their semantics:  *)

  type procedure_call_t = 
    supplied_parameter_t list
  and supplied_parameter_t =
    | SuppliedValue of t
    | SuppliedDesignator of t
end


(* ------------------------------------------------------------------------- *)
(* Type Rules *)
(* ------------------------------------------------------------------------- *)

module TypeRules
  (Name: NAME) 
  (GlobalName: NAME) 
  (Type: TYPE with type name_t = Name.t and type globalname_t = GlobalName.t)
  (Interface: INTERFACE with type type_t = Type.t and type globalname_t = GlobalName.t)
  = 
struct

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)
(* Type Categories *)
(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)

let atomic_type (t: Type.t) : bool = 
  match t with
  | Integer | Byte | Word | Real | Boolean
  | Ref _ | NamedRef _ -> true
  | _ -> false

let structured_type (t: Type.t) : bool =  
  match t with
  | Array _ | OpenArray _ | Record _ | Procedure (_, _) -> true
  | Opaque _ -> true
  | _ -> false 

let value_type t = atomic_type t || t = Nil   

let return_type t = atomic_type t || t = Statement

let reference_type (t: Type.t) : bool = 
  match t with
  | Nil | Ref _ | NamedRef _ -> true
  | _ -> false

let referenceable_type t = atomic_type t || structured_type t

let sized_type (t: Type.t) : bool =  
  (* can be stored in variables and assigned *) 
  match t with
  | Array _  | Record _ -> true
  | _ -> atomic_type t 


(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)
(* Type Validity *)
(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)

let rec valid_type (m:Interface.t) (t: Type.t) : bool =
  match t with
  | Ref rt -> valid_type m rt && referenceable_type t
  | Array (len, et) -> len > 0 && valid_type m et && sized_type et 
  | OpenArray et -> sized_type et && valid_type m et
  | Record es -> valid_elements m es
  | Procedure (ps, rt) -> valid_parameters m ps && return_type rt && valid_type m rt
  | NamedRef n -> Option.is_some (Interface.get_type m n)  
  | Opaque n -> Option.is_some (Interface.get_type m n)  
  | _ -> true

and valid_elements m (es: Type.element_t list) : bool =
  let ns, ts = List.split es in
  not (Utility.distinct Name.equal ns) && 
  List.for_all (fun t -> sized_type t && valid_type m t) ts

and valid_parameters m (ps: Type.parameter_t list) : bool =
  let valid_parameter = function
  | (Type.ByReference, t) -> valid_type m t && referenceable_type t 
  | (Type.ByValue, t) -> valid_type m t && (value_type t || referenceable_type t)
  in 
  List.for_all valid_parameter ps


(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)
(* Type Equality *)
(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)

(** [equal a b] is true if types [a] and [b] are equal.  

    Opaque types have names, records can have names. Two named types are 
    equal if they have the same name or if they have been declared 
    equivalent by a type constraint in a functor. Named types are always 
    considered to be structured types. *)

let rec equal (m: Interface.t) (a: Type.t) (b: Type.t): bool =
  match a, b with
  | Ref t1, Ref t2 -> equal m t1 t2
  | NamedRef n1, NamedRef n2 -> Interface.equivalent m n1 n2 
  | Array (len1, t1), Array (len2, t2) -> len1 = len2 && equal m t1 t2
  | OpenArray t1, OpenArray t2 -> equal m t1 t2
  | Record e1, Record e2 -> equal_elements m e1 e2
  | Opaque n1, Opaque n2 -> Interface.equivalent m n1 n2
  | Procedure (p1, t1), Procedure (p2, t2) -> 
      equal_parameters m p1 p2 && equal m t1 t2
  | _ -> true


(* Lists of procedure parameters are equal if the parameters from each list 
   can be paired, and each pair of parameters has an equal passing method and 
   type. *)

and equal_parameters 
    (m: Interface.t) 
    (ps1: Type.parameter_t list) 
    (ps2: Type.parameter_t list) : bool =
  let equal_parameter (pm1, t1) (pm2, t2) = equal m t1 t2 && pm1 = pm2 in
  List.length ps1 = List.length ps2 &&
  List.for_all2 equal_parameter ps1 ps2


(* Lists of record elements are equal if the elements from each list can be
   paired, and each pair has an equal name and type. *)

and equal_elements 
    (m: Interface.t)
    (es1: Type.element_t list)
    (es2 : Type.element_t list) : bool =
  let equal_element (n1, t1) (n2, t2) = Name.equal n1 n2 && equal m t1 t2 in
  List.length es1 = List.length es2 &&
  List.for_all2 equal_element es1 es2


(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)
(* Assignment Compatibilities *)
(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)


(** [assignment_compatible dst src] is true if a variable of type [dst] can be
    assigned a value of type [src].

    Two types are assignment compatible if they are sized and have equal types.
    In addition, any reference can be assigned [nil] and a reference
    to a procedure can be assigned a procedure of the correct type. *)

let assignment_compatible (m: Interface.t) (dst: Type.t) (src: Type.t) : bool =
  sized_type dst && sized_type src && src = dst ||
  reference_type dst && src = Nil ||
  match dst, src with
  | Ref (Procedure (dp, dr)), Procedure (sp, sr) -> 
      equal_parameters m dp sp && equal m dr sr
  | _ -> false 


(** [reference_parameter_compatible dst src] is true if a designator of type
    [src] can by passed by reference to a procedure parameter of type [dst].

    An actual parameter supplied to a procedure parameter must have an equal type. 
    The exception is that arrays are compatible with open arrays if their 
    element types are equal. *)

let reference_parameter_compatible (m: Interface.t) (dst: Type.t) (src: Type.t) : bool =
  match dst, src with
  | OpenArray t1, Array (_, t2) -> equal m t1 t2
  | OpenArray t1, OpenArray t2 -> equal m t1 t2
  | t1, t2 -> equal m t1 t2


(** [value_parameter_compatible dst src] is true if a designator of type
    [src] can by passed by value to a procedure parameter of type [dst].

    The supplied parameter must be assignment compatible with the procedure 
    parameter. The exception is that arrays are compatible with open arrays 
    if their element types are equal m. *)

let value_parameter_compatible (m: Interface.t) (dst: Type.t) (src: Type.t) : bool =
  match dst, src with
  | OpenArray t1, Array (_, t2) -> equal m t1 t2
  | OpenArray t1, OpenArray t2 -> equal m t1 t2
  | t1, t2 -> assignment_compatible m t1 t2


(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)
(* Procedure Call Validity *)
(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)


(** [procedure_call_valid] is true if there are 
    the same number of supplied call parameters as procedure parameters, 
    by-reference parameters are supplied designators, and the types of each 
    pair of procedure parameter and supplied parameter are compatible. *)

let procedure_call_valid
    (m: Interface.t)
    (procedure_parameters: Type.parameter_t list)
    (supplied_parameters: Type.supplied_parameter_t list) : bool =
  let parameter_compatible p s =
    match p, s with
    | (Type.ByValue, pt), Type.SuppliedValue st -> 
        value_parameter_compatible m pt st
    | (Type.ByValue, pt), Type.SuppliedDesignator st -> 
        value_parameter_compatible m pt st
    | (Type.ByReference, pt), Type.SuppliedDesignator st -> 
        reference_parameter_compatible m pt st
    | (Type.ByReference, _), Type.SuppliedValue _ -> 
        false
  in
  List.length procedure_parameters = List.length supplied_parameters &&
  List.for_all2 parameter_compatible procedure_parameters supplied_parameters

end (* module TypeRules *)


(* ------------------------------------------------------------------------- *)
(* Type Descriptions *)
(* ------------------------------------------------------------------------- *)

(* "TypeDescription.t" is for types reported by the compiler. They are not quite
  the same. These include types defined by name which aren't records or opaque
  types, e.g "type char = byte". These have to be expanded to produce the
  "Type.t" types described above. "TypeDescriptions.expand" does this, and also
  checks the type descriptions for validity, return None for invalid descriptions.

  I will need to check this in Coq:

    Theorem TypeDescription_expansion_returns_valid_types : 
      forall (d: TypeDescription_t) (t: Type_t), 
      TypeDescription_expand d = (Some t) -> Rules_valid t.
*)

module TypeDescription
  (Name: NAME) 
  (GlobalName: NAME) 
  (Type: TYPE with type name_t = Name.t and type globalname_t = GlobalName.t)
  (Interface: INTERFACE with type type_t = Type.t and type globalname_t = GlobalName.t)
  = 
struct

  module Rule = TypeRules(Name)(GlobalName)(Type)(Interface)

type t =
  | Named of GlobalName.t                     
  | Integer
  | Byte
  | Word
  | Real
  | Boolean
  | Ref of t
  | Nil 
  | Array of int * t
  | OpenArray of t
  | Record of element_t list
  | Procedure of parameter_t list * t option

and element_t = Name.t * t

and parameter_t = 
  Type.passing_method_t * t

open Utility.OptionMonad

let rec expand (m: Interface.t) (d : t) : Type.t option = 
  match d with
  | Named n -> Interface.get_type m n
  | Integer -> return Type.Integer
  | Byte -> return Type.Byte
  | Word -> return Type.Word
  | Real -> return Type.Real
  | Boolean -> return Type.Boolean
  | Ref d -> expand_ref m d
  | Nil -> return Type.Nil
  | Array (i, d) -> expand_array m i d
  | OpenArray d -> let* t = expand m d in return (Type.OpenArray t)
  | Record es -> expand_record m es
  | Procedure (ps, d) -> expand_procedure m ps d

and expand_array m i d = 
  if i <= 0 then 
    None 
  else
    let* t = expand m d in 
    return (Type.Array (i, t))

and expand_ref m d = 
  match d with
  | Named n -> 
      let* t = Interface.get_type m n in
      if Rule.structured_type t 
      then return (Type.NamedRef n)
      else return (Type.Ref t)       
  | d ->
      let* t = expand m d in 
      return (Type.Ref t)

and expand_record m es =
  if Utility.distinct (Name.equal) (fst (List.split es)) &&  
     List.length es > 0
  then
    let expand_element (n, d) = (let* t = expand m d in return (n, t)) in
    let* es' = map_option es expand_element in 
    return (Type.Record es')
  else
    None
    
and expand_procedure m ps d =
  let expand_parameter (p, d) =  (let* t = expand m d in return (p, t)) in
  let* ps' = map_option ps expand_parameter in
  match d with  (* Does it have a return type? *)
  | None -> return (Type.Procedure (ps', Statement))
  | Some rd ->
      let* t = expand m rd in
      return (Type.Procedure (ps', t))

end  (* module TypeDescriptions *)
