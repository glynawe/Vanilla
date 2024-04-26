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
  | Boolean
  | Ref of t
  | Nil
  | Array of int * t
  | OpenArray of t


(* ------------------------------------------------------------------------------- *)
(* Type Equality *)
(* ------------------------------------------------------------------------------- *)

(** [equal a b] True if types [a] and [b] are equal by structural equivalence. *)

let rec equal (a: t) (b: t): bool =
  match a, b with
  | Integer, Integer
  | Boolean, Boolean
  | Nil, Nil -> true
  | Ref t1, Ref t2 -> equal t1 t2
  | Array (len1, t1), Array (len2, t2) -> len1 = len2 && equal t1 t2
  | OpenArray t1, OpenArray t2 -> equal t1 t2
  | _ -> false


(* ------------------------------------------------------------------------------- *)
(* Type Validity *)
(* ------------------------------------------------------------------------------- *)


(** [valid_value a] is true if type [a] is an acceptable expression value.  *)

(** [valid_reference a] is true if type [a] can be used as a reference type target
    or a procedure parameter. *)

(** [valid_variable a] is true if type [a] can be stored in a variable,
    is assignable and is otherwise generally valid.  *)

let rec valid_value (a: t) : bool =
  match a with
  | Integer -> true
  | Boolean -> true
  | Ref b -> valid_reference b
  | Nil -> true
  | _ -> false

and valid_reference (a: t) : bool =
  match a with
  | OpenArray a -> valid_variable a
  | Nil -> false
  | a -> valid_variable a

and valid_variable (a: t) : bool =
  match a with
  | Array (d, e) -> d > 0 && valid_variable e
  | Nil -> false
  | a -> valid_value a


(* ------------------------------------------------------------------------------- *)
(* Assignment Compatibilities *)
(* ------------------------------------------------------------------------------- *)


(** [assignment_compatible dst src] is true if a variable of type [dst] can be
    assigned a value of type [src].

    Two types are usually assignment compatible if they have equal types.
    The exceptions are that any reference can be assigned [nil]. *)

(** [var_parameter_compatible dst src] is true if a designator of type
    [src] can by supplied to a procedure parameter of type [dst].

    A supplied parameter is type compatible with a [var] formal parameter if
    their types are equal. The exception is that arrays are compatible
    with open arrays if their element types are equal. *)

(** [value_parameter_type_compatible dst src] is true if a value of type
    [src] can by supplied to a value parameter of type [dst].

    An supplied parameter is type compatible with a value formal parameter if
    their types are equal. The exception is that arrays are compatible
    with open arrays if their element types are equal. *)

let assignment_compatible (dst: t) (src: t) : bool =
  match dst, src with
  | Ref _, Nil -> true
  | (Nil | OpenArray _ ), _ -> false
  | _, (Nil | OpenArray _) -> false
  | t1, t2 -> equal t1 t2

let var_parameter_compatible (dst: t) (src: t) : bool =
  match dst, src with
  | OpenArray t1, Array (_, t2) -> equal t1 t2
  | OpenArray t1, OpenArray t2 -> equal t1 t2
  | t1, t2 -> equal t1 t2

let value_parameter_compatible (dst: t) (src: t) : bool =
  match dst, src with
  | OpenArray t1, Array (_, t2) -> equal t1 t2
  | OpenArray t1, OpenArray t2 -> equal t1 t2
  | t1, t2 -> assignment_compatible t1 t2
