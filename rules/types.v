(* The Vanilla type rules in Gallina. *)

(* These functions return bool, though perhaps they need to be propositions. *)

(* Not dealt with: anonymous types, which are allowed in interfaces. *)
(* Not dealt with: recurive reference-to-record types. XXX *)

Require Import Coq.Lists.List.
Import ListNotations.
Require Coq.Strings.String.
Open Scope bool_scope.


(* -------------------------------------------------------------------------- *)
(* Names *)
(* -------------------------------------------------------------------------- *)

Definition name_t := Coq.Strings.String.string.

Definition name_eqb := Coq.Strings.String.eqb.

Fixpoint name_not_in (n: name_t) (ns: list name_t) : bool :=
  match ns with
  | [] => true
  | n' :: ns' => if name_eqb n n' then false else name_not_in n ns'
  end. 


(* -------------------------------------------------------------------------- *)
(* Types *)
(* -------------------------------------------------------------------------- *)


Inductive passing_t : Type := ByReference | ByValue.


Inductive type_t : Type :=

  (* Atomic types. *)
  | Integer
  | Boolean
  | Byte
  | Word
  | Real
  | Reference (rt: type_t)
  | NilReference
  
  (* Structured types. *)
  | Array (length: nat) (element: type_t)
  | OpenArray (element: type_t)   (* length only known at runtime *)
  | Record (elements: list (name_t * type_t))
  | Procedure (parameters: list (name_t * passing_t * type_t)) 
              (return_type: type_t)
  
  (* The "type" of proper procedures statements. Like C's void. *)
  | Statement.


Definition passing_eqb a b := 
  match a, b with
  | ByReference, ByReference => true
  | ByValue, ByValue => true
  | _, _ => false
  end.


(* -------------------------------------------------------------------------- *)
(* Type Equality *)
(* -------------------------------------------------------------------------- *)


(** [equal a b] is true if types [a] and [b] are structurally equivalent. 

  Lists of procedure parameters are equal if the parameters from each list can 
  be paired, and each pair of parameters has an equal parameter passing method 
  and type. (Parameter names are ignored, they are just placeholders.)

  Lists of record elements are equal if the elements from each list be paired,
  and each pair of elements has the an equal name and equal type. *)

Fixpoint equal (t1: type_t) (t2: type_t) : bool :=
  match t1, t2 with
  | Integer, Integer => true
  | Boolean, Boolean => true
  | Byte, Byte => true
  | Word, Word => true
  | Real, Real => true
  | NilReference, NilReference => true
  | Reference rt1, Reference rt2 => equal rt1 rt2  
  | Array len1 et1, Array len2 et2 => Nat.eqb len1 len2 && equal et1 et2
  | OpenArray et1, OpenArray et2 => equal et1 et2
  | Record es1, Record es2 =>
    (fix equal_elements xs ys :=    (* Gallina requires this nesting :-\ *)
      match xs, ys with
      | (n1, t1) :: xs', (n2, t2) :: ys' => 
          name_eqb n1 n2 && equal t1 t2 && equal_elements xs' ys'
      | [], [] => true
      | _, _ => false
      end
    ) es1 es2
  | Procedure ps1 rt1, Procedure ps2 rt2 =>
    equal rt1 rt2 &&
    (fix equal_parameters xs ys :=
      match xs, ys with
      | (_, p1, t1) :: xs', (_, p2, t2) :: ys' => 
          passing_eqb p1 p2 && equal t1 t2 && equal_parameters xs' ys'
      | [], [] => true
      | _, _ => false
      end
    ) ps1 ps2
  | Statement, Statement => true
  | _, _ => false 
  end.


(* -------------------------------------------------------------------------- *)
(* Type Validity *)
(* -------------------------------------------------------------------------- *)


(** [valid_variable a] is true if type [a] can be stored in a variable, or is
    assignable.  (Vanilla's assignment operator works on equally-typed records 
    and arrays. *)

Fixpoint valid_variable (t: type_t) : bool :=
  match t with
  | Integer => true
  | Boolean => true
  | Byte => true
  | Word => true
  | Real => true
  | Reference rt => valid_reference rt
  | NilReference => false
  | Array len et => Nat.ltb 0 len && valid_variable et
  | OpenArray _ => false
  | Record es =>
      Nat.ltb 0 (length es) &&
      (fix element_test es ns :=
        match es, ns with
        | [], _ => true
        | (n, t) :: es', ns => 
            name_not_in n ns && valid_variable t && 
            element_test es' (n :: ns) 
        end  
      ) es []
  | Procedure _ _ => false
  | Statement => false
  end


(** [valid_reference a] is true if type [a] can be used as a reference type 
    target or a pass-by-reference procedure parameter. *)

with valid_reference (t: type_t) : bool :=
  match t with
  | Statement => false
  | Integer => true
  | Boolean => true
  | Byte => true
  | Word => true
  | Real => true
  | Reference rt => valid_reference rt
  | NilReference => false
  | Array len et => Nat.ltb 0 len && valid_variable et
  | OpenArray a => valid_variable a

  | Record es =>
      Nat.ltb 0 (length es) &&
      (fix element_test es ns :=
        match es, ns with
        | [], _ => true
        | (n, t) :: es', ns => 
            name_not_in n ns && valid_variable t && 
            element_test es' (n :: ns) 
        end) es []

  | Procedure ps rt =>
      valid_return rt &&
      (fix parameter_test ps :=
        match ps with
        | [] => true
        | (_, ByReference, t) :: ps' => valid_reference t && parameter_test ps'
        | (_, ByValue, t) :: ps' => valid_parameter t && parameter_test ps'
        end) ps
  end


(** [valid_parameter a] is true if type [a] can be used as a value procedure 
    parameter. (Structured types are allowed. They are passed by reference, 
    but value parameters are immutuable within the called procedure.) *)

with valid_parameter (t: type_t) : bool :=
  match t with
  | Statement => false
  | Integer => true
  | Boolean => true
  | Byte => true
  | Word => true
  | Real => true
  | Reference rt => valid_reference rt
  | NilReference => true
  | Array _ _ => false
  | OpenArray a => valid_variable a
  | Record _ => false

  | Procedure ps rt =>
      valid_return rt &&
      (fix parameter_test ps :=
        match ps with
        | [] => true
        | (_, ByReference, t) :: ps' => valid_reference t && parameter_test ps'
        | (_, ByValue, t) :: ps' => valid_parameter t && parameter_test ps'
        end) ps
  end

with valid_return (t: type_t) : bool :=
  match t with
  | Integer => true
  | Boolean => true
  | Byte => true
  | Word => true
  | Real => true
  | Reference rt => valid_reference rt
  | NilReference => true
  | Array _ _ => false
  | OpenArray _ => false
  | Record _ => false
  | Procedure _ _ => false
  | Statement => true   (* proper procedures do not have return values *) 
  end.


(** [valid_value t] is true if type [t] is an acceptable expression value. 
    (Vanilla expressions have atomic types.) *)

Definition valid_value (t: type_t) : bool :=
  match t with
  | Integer => true
  | Boolean => true
  | Byte => true
  | Word => true
  | Real => true
  | Reference rt => valid_reference rt
  | NilReference => true
  | Array _ _ => false
  | OpenArray _ => false
  | Record _ => false
  | Procedure _ _ => false
  | Statement => false
  end.

(* -------------------------------------------------------------------------- *)
(* Assignment Compatibilities *)
(* -------------------------------------------------------------------------- *)


(** [assignment_compatible dst src] is true if a variable of type [dst] can be
    assigned a value of type [src].

    Two types are usually assignment compatible if they have equal types.
    The exceptions are that any reference can be assigned [nil] and a reference
    to a procedure can be assigned a procedure of the correct type.
    But otherwise open arrays, procedures and statements cannot be assigned. *)


Definition assignment_compatible (dst: type_t) (src: type_t) : bool :=
  match dst, src with
  | Reference _,  NilReference => true
  | NilReference, _            => false
  | OpenArray _,  _            => false
  | _,            OpenArray _  => false
  | t1,           t2           => equal t1 t2
  end.


(** [var_parameter_compatible dst src] is true if a designator of type
    [src] can by supplied to a pass-by-reference procedure parameter of 
    type [dst].

    A supplied parameter is type compatible with a [var] formal parameter if
    their types are equal. The exception is that arrays are compatible with 
    open arrays if their element types are equal. *)

Definition var_parameter_compatible (dst: type_t) (src: type_t) : bool :=
  match dst, src with
  | OpenArray et1,  Array _ et2  => equal et1 et2
  | t1,             t2           => equal t1 t2
  end.


(** [value_parameter_type_compatible dst src] is true if a value of type
    [src] can by supplied to a pass-by-value parameter of type [dst].

    An supplied parameter is type compatible with a value formal parameter if
    their types are equal. The exception is that arrays are compatible
    with open arrays if their element types are equal. *)

Definition value_parameter_compatible (dst: type_t) (src: type_t) : bool :=
  match dst, src with
  | OpenArray et1,  Array _ et2    => equal et1 et2
  | OpenArray et1,  OpenArray et2  => equal et1 et2
  | t1,             t2             => assignment_compatible t1 t2
  end.


(* -------------------------------------------------------------------------- *)
(* Procedure Call Validity *)
(* -------------------------------------------------------------------------- *)

(** [procedure_call_valid] is true if: there are the same number of supplied 
    call parameters as procedure parameters; pass-by-reference parameters are 
    supplied designators, not values; and the types of each pair of procedure 
    parameter and supplied parameter are compatible. *)

Inductive call_parameter_t : Type :=
  | SuppliedValue (value: type_t)
  | SuppliedDesignator (designator: type_t).


Definition parameter_pair_compatible 
      (param_pair: (name_t * passing_t * type_t) * call_parameter_t) : bool :=
  match param_pair with
  | ((_, ByValue, pt), SuppliedValue st) => 
      value_parameter_compatible pt st
  | ((_, ByValue, pt), SuppliedDesignator st) => 
      value_parameter_compatible pt st
  | ((_, ByReference, _), SuppliedValue _) => 
      false
  | ((_, ByReference, pt), SuppliedDesignator st) => 
      var_parameter_compatible pt st
  end.

Definition procedure_call_valid
    (parameters: list (name_t * passing_t * type_t))
    (supplied: list call_parameter_t) : bool :=
  Nat.eqb (length parameters) (length supplied) &&
  forallb parameter_pair_compatible (combine parameters supplied).
