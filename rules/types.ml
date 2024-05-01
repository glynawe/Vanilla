(* The Vanilla type rules in OCaml. *)


(* ------------------------------------------------------------------------- *)
(* Names *)
(* ------------------------------------------------------------------------- *)


module Name = struct
  type t = string
  let equal = String.equal
end


module GlobalName = struct
  type t = 
    | Imported of Name.t * Name.t
    | Included of Name.t
  (* Two names are equivalent if they are equal or if they have been declared 
    equivalent by a functor. *)
  let equivalent (a: t) (b: t) : bool = true  (* dummy *)
end


let rec all_different : Name.t list -> bool =
  function
  | [] -> true
  | n :: ns -> not (List.exists (Name.equal n) ns) && all_different ns


(* ------------------------------------------------------------------------- *)
(* Types *)
(* ------------------------------------------------------------------------- *)

type type_t =
  | Statement                     
  | Integer
  | Byte
  | Word
  | Real
  | Boolean
  | Ref of type_t
  | NamedRef of GlobalName.t  (* refers to a record or abstract type *)
  | Nil                       (* compatible with any reference *)
  | Array of int * type_t
  | OpenArray of type_t       (* Array whose length is only known at runtime.*)
  | Record of element_t list
  | Abstract of GlobalName.t
  | Procedure of parameter_t list * type_t

and parameter_t = Name.t * passing_method_t * type_t

and passing_method_t = ByReference | ByValue

and element_t = Name.t * type_t

let atomic_type t = 
  match t with
  | Integer | Byte | Word | Real | Boolean
  | Ref _ | NamedRef _ -> true
  | _ -> false

let structured_type t = 
  match t with
  | Array _ | OpenArray _ | Record _ | Procedure (_, _) -> true
  | Abstract _ -> true
  | _ -> false 

let value_type t = atomic_type t || t = Nil   

let return_type t = atomic_type t || t = Statement

let reference_type t = 
  match t with
  | Nil | Ref _ | NamedRef _ -> true
  | _ -> false

let referenceable_type t = atomic_type t || structured_type t

let sized_type t =  (* can be stored in variables and assigned *) 
  match t with
  | Array _  | Record _ -> true
  | _ -> atomic_type t 


(* -------------------------------------------------------------------------- *)
(* Type Equality *)
(* -------------------------------------------------------------------------- *)

(** [equal a b] is true if types [a] and [b] are equal.  

    Abstract types have names, records can have names. Two named types are 
    equal if they are the same name or if they have been declared 
    equivalent by a functor. Named types are always considered to be 
    structured types. *)

let rec equal (a: type_t) (b: type_t): bool =
  match a, b with
  | Ref t1, Ref t2 -> equal t1 t2
  | NamedRef n1, NamedRef n2 -> GlobalName.equivalent n1 n2 
  | Array (len1, t1), Array (len2, t2) -> len1 = len2 && equal t1 t2
  | OpenArray t1, OpenArray t2 -> equal t1 t2
  | Record e1, Record e2 -> equal_elements e1 e2
  | Abstract n1, Abstract n2 -> GlobalName.equivalent n1 n2
  | Procedure (p1, t1), Procedure (p2, t2) -> equal_parameters p1 p2 && equal t1 t2
  | _ -> true


(* Lists of procedure parameters are equal if the parameters from each list 
   can be paired, and each pair of parameters has an equal passing method and 
   type. (Parameter names are ignored, they are just placeholders.) *)

and equal_parameters (ps1: parameter_t list) (ps2: parameter_t list): bool =
  let equal_parameter (_, pm1, t1) (_, pm2, t2) = equal t1 t2 && pm1 = pm2 in
  List.length ps1 = List.length ps2 &&
  List.for_all2 equal_parameter ps1 ps2


(* Lists of record elements are equal if the elements from each list can be
   paired, and each pair of element has an equal name and type. *)

and equal_elements (es1: element_t list) (es2 : element_t list) : bool =
  let equal_element (n1, t1) (n2, t2) = Name.equal n1 n2 && equal t1 t2 in
  List.length es1 = List.length es2 &&
  List.for_all2 equal_element es1 es2


(* ------------------------------------------------------------------------- *)
(* Type Validity *)
(* ------------------------------------------------------------------------- *)

let rec valid_type t =
  match t with
  | Ref rt -> valid_type rt && referenceable_type t
  | Array (len, et) -> len > 0 && valid_type et && sized_type et 
  | OpenArray et -> sized_type et && valid_type et
  | Record es -> valid_elements es
  | Procedure (ps, rt) -> valid_parameters ps && return_type rt && valid_type rt
  | _ -> true

and valid_elements es =
  let ns, ts = List.split es in
  all_different ns && 
  List.for_all (fun t -> sized_type t && valid_type t) ts

and valid_parameters ps =
  let valid_parameter = function
  | (_, ByReference, t) -> valid_type t && referenceable_type t 
  | (_, ByValue, t) -> valid_type t && (value_type t || referenceable_type t)
  in 
  List.for_all valid_parameter ps


(* -------------------------------------------------------------------------- *)
(* Assignment Compatibilities *)
(* -------------------------------------------------------------------------- *)


(** [assignment_compatible dst src] is true if a variable of type [dst] can be
    assigned a value of type [src].

    Two types are assignment compatible if they are sized and have equal types.
    In addition, any reference can be assigned [nil] and a reference
    to a procedure can be assigned a procedure of the correct type. *)

let assignment_compatible (dst: type_t) (src: type_t) : bool =
  sized_type dst && sized_type src && src = dst ||
  reference_type dst && src = Nil ||
  match dst, src with
  | Ref (Procedure (dp, dr)), Procedure (sp, sr) -> 
      equal_parameters dp sp && equal dr sr
  | _ -> false 


(** [reference_parameter_compatible dst src] is true if a designator of type
    [src] can by passed by reference to a procedure parameter of type [dst].

    The supplied parameter an procedure parameter must have equal types. 
    The exception is that arrays are compatible with open arrays if their 
    element types are equal. *)

let reference_parameter_compatible (dst: type_t) (src: type_t) : bool =
  match dst, src with
  | OpenArray t1, Array (_, t2) -> equal t1 t2
  | OpenArray t1, OpenArray t2 -> equal t1 t2
  | t1, t2 -> equal t1 t2


(** [value_parameter_compatible dst src] is true if a designator of type
    [src] can by passed by value to a procedure parameter of type [dst].

    The supplied parameter must be assignment compatiable with the procedure 
    parameter. The exception is that arrays are compatible with open arrays 
    if their element types are equal. *)

let value_parameter_compatible (dst: type_t) (src: type_t) : bool =
  match dst, src with
  | OpenArray t1, Array (_, t2) -> equal t1 t2
  | OpenArray t1, OpenArray t2 -> equal t1 t2
  | t1, t2 -> assignment_compatible t1 t2


(* -------------------------------------------------------------------------- *)
(* Procedure Call Validity *)
(* -------------------------------------------------------------------------- *)


type procedure_call_t =
  supplied_parameter_t list

and supplied_parameter_t =
  | SuppliedValue      of type_t
  | SuppliedDesignator of type_t


let parameter_compatible p s =
  match p, s with
  | (_, ByValue, pt), SuppliedValue st -> value_parameter_compatible pt st
  | (_, ByValue, pt), SuppliedDesignator st -> value_parameter_compatible pt st
  | (_, ByReference, pt), SuppliedDesignator st -> reference_parameter_compatible pt st
  | (_, ByReference, _), SuppliedValue _ -> false


(** [procedure_call_valid] is true if there are 
    the same number of supplied call parameters as procedure parameters, 
    by-reference parameters are supplied designators, and the types of each 
    pair of procedure parameter and supplied parameter are compatible. *)

let procedure_call_valid
    (procedure_parameters: parameter_t list)
    (supplied_parameters: supplied_parameter_t list) : bool =
  List.length procedure_parameters = List.length supplied_parameters &&
  List.for_all2 parameter_compatible procedure_parameters supplied_parameters
