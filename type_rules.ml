(* The Vanilla type rules in OCaml. *)


(* Identifiers. (Note: this is a dummy, Name.t and Name.equal will be defined elsewhere.) *)
module Name = struct
  type t = string
  let equal = String.equal
  let rec all_different : t list -> bool =
    function
    | [] -> true
    | n :: ns -> not (List.exists (equal n) ns) && all_different ns
end


(* ------------------------------------------------------------------------------- *)
(* Types *)
(* ------------------------------------------------------------------------------- *)


type t =
  | Integer
  | Byte
  | Word
  | Real
  | Boolean
  | Statement                     (* The type of statements. (Like C's void.) *)
  | Ref of t
  | Nil                           (* compatible with any reference *)
  | Array of int * t
  | OpenArray of t                (* Array whose length is only known at runtime.*)
  | Record of (Name.t * t) list
  | Procedure of parameter_t list * t

and parameter_t =
  |  VarParameter of Name.t * t
  |  ValueParameter of Name.t * t


type procedure_call_t =
  Call of call_parameter_t list

and call_parameter_t =
  | SuppliedValue of t
  | SuppliedDesignator of t


let parameter_type (p: parameter_t): t =
  match p with
  | VarParameter (_, pt) -> pt
  | ValueParameter (_, pt) -> pt


(* ------------------------------------------------------------------------------- *)
(* Type Equality *)
(* ------------------------------------------------------------------------------- *)


(** [equal a b] True if types [a] and [b] are equal by structural equivalence. *)

let rec equal (a: t) (b: t): bool =
  match a, b with
  | Integer, Integer
  | Byte, Byte
  | Word, Word
  | Real, Real
  | Boolean, Boolean
  | Nil, Nil
  | Statement, Statement -> true
  | Ref t1, Ref t2 -> equal t1 t2
  | Array (len1, t1), Array (len2, t2) -> len1 = len2 && equal t1 t2
  | Procedure (p1, t1), Procedure (p2, t2) -> equal_parameters p1 p2 && equal t1 t2
  | OpenArray t1, OpenArray t2 -> equal t1 t2
  | Record e1, Record e2 -> equal_elements e1 e2
  | _ -> false

(* Lists of procedure parameters are equal if the parameters from each list can be
   paired, and each pair of parameters has an equal passing method (var or val) and type.
   (Parameter names are ignored, they are just placeholders.) *)

and equal_parameters (p1: parameter_t list) (p2: parameter_t list): bool =
  match p1, p2 with
  | VarParameter (_, t1) :: p1', VarParameter (_, t2) :: p2' ->
      equal t1 t2 && equal_parameters p1' p2'
  | ValueParameter (_, t1) :: p1', ValueParameter (_, t2) :: p2' ->
      equal t1 t2 && equal_parameters p1' p2'
  | [], [] -> true
  | _ -> false

(* Lists of record elements are equal if the elements from each list be paired,
    and each pair of elements has the an equal name and equal type. *)

and equal_elements (e1: (Name.t * t) list) (e2 : (Name.t * t) list) : bool =
  match e1, e2 with
  | (n1, t1) :: e1', (n2, t2) :: e2' -> Name.equal n1 n2 && equal t1 t2 && equal_elements e1' e2'
  | [], [] -> true
  | _ -> false


(* ------------------------------------------------------------------------------- *)
(* Type Validity *)
(* ------------------------------------------------------------------------------- *)


(** [valid_value a] is true if type [a] is an acceptable expression value.  *)

let rec valid_value (a: t) : bool =
  match a with
  | Integer | Byte | Word | Real | Boolean -> true
  | Ref b -> valid_target b
  | Nil -> true
  | _ -> false

(** [valid_target a] is true if type [a] can be used as a reference type target
    or a procedure parameter. *)

and valid_target (a: t) : bool =
  match a with
  | OpenArray a -> valid_variable a
  | Procedure (ps, rt) -> List.for_all valid_target (List.map parameter_type ps) && valid_return rt
  | a -> valid_variable a


(** [valid_variable a] is true if type [a] can be stored in a variable,
    is assignable and is otherwise generally valid.  *)

and valid_variable a =
  match a with
  | Array (d, e) -> d > 0 && valid_variable e
  | Record es ->
      let ns, ts = List.split es in
      List.length es > 0 && Name.all_different ns && List.for_all valid_variable ts
  | a -> valid_value a

(** [valid_return a] is true if type [a] can be returned by a procedure. *)

and valid_return (a: t) : bool =
  match a with
  | Statement -> true
  | a -> valid_value a


(* ------------------------------------------------------------------------------- *)
(* Assignment Compatibilities *)
(* ------------------------------------------------------------------------------- *)


(** [assignment_compatible dst src] is true if a variable of type [dst] can be
    assigned a value of type [src].

    Two types are usually assignment compatible if they have equal types.
    The exceptions are that any reference can be assigned [nil] and a reference
    to a procedure can be assigned a procedure of the correct type.
    But otherwise open arrays, procedures and statements cannot be assigned. *)

let assignment_compatible (dst: t) (src: t) : bool =
  match dst, src with
  | Ref _, Nil -> true
  | Ref (Procedure (_, _) as a), (Procedure (_, _) as b) -> equal a b
  | (Nil | OpenArray _ | Statement | Procedure (_,_)), _ -> false
  | _, (Nil | OpenArray _ | Statement | Procedure (_,_)) -> false
  | t1, t2 -> equal t1 t2


(** [var_parameter_compatible dst src] is true if a designator of type
    [src] can by supplied to a procedure parameter of type [dst].

    A supplied parameter is type compatible with a [var] formal parameter if
    their types are equal. The exception is that arrays are compatible
    with open arrays if their element types are equal. *)

let var_parameter_compatible (dst: t) (src: t) : bool =
  match dst, src with
  | OpenArray t1, Array (_, t2) -> equal t1 t2
  | OpenArray t1, OpenArray t2 -> equal t1 t2
  | t1, t2 -> equal t1 t2


(** [value_parameter_type_compatible dst src] is true if a value of type
    [src] can by supplied to a value parameter of type [dst].

    An supplied parameter is type compatible with a value formal parameter if
    their types are equal. The exception is that arrays are compatible
    with open arrays if their element types are equal. *)

let value_parameter_compatible (dst: t) (src: t) : bool =
  match dst, src with
  | OpenArray t1, Array (_, t2) -> equal t1 t2
  | OpenArray t1, OpenArray t2 -> equal t1 t2
  | t1, t2 -> assignment_compatible t1 t2


(* ------------------------------------------------------------------------------- *)
(* Procedure Call Validity *)
(* ------------------------------------------------------------------------------- *)

(** [procedure_call_valid procedure_type call_parameters] is true if there are the
    same number of supplied call parameters as procedure parameters, [var] parameters
    are supplied designators, not values, and the types of each pair of procedure
    parameter and supplied parameter are compatible. *)

let procedure_call_valid
    (Procedure (procedure_parameters, _): t)
    (call_parameters: call_parameter_t list) : bool =
  let parameter_compatible (p, s) =
    match p, s with
    | ValueParameter (_, pt), SuppliedValue      st -> value_parameter_compatible pt st
    | ValueParameter (_, pt), SuppliedDesignator st -> value_parameter_compatible pt st
    | VarParameter (_, pt),   SuppliedValue      st -> false
    | VarParameter (_, pt),   SuppliedDesignator st -> var_parameter_compatible pt st
  in
  List.length procedure_parameters = List.length call_parameters &&
  List.for_all parameter_compatible (List.combine procedure_parameters call_parameters)
