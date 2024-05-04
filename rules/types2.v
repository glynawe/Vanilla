(* The Vanilla type rules in Gallina. *)

(* Not dealt with: anonymous types, which are allowed in interfaces. *)
(* Not dealt with: recursive reference-to-record types. XXX *)

Require Import Coq.Lists.List.
Import ListNotations.
Require Coq.Strings.String.
Open Scope bool_scope.


(* -------------------------------------------------------------------------- *)
(* Types *)
(* -------------------------------------------------------------------------- *)


Definition name_t := Coq.Strings.String.string.

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
  
  (* The "type" of proper procedures and statements. *)
  | Statement.
  
Definition parameter_t : Type := name_t * passing_t * type_t.

Definition procedure_t : Type := list parameter_t * type_t.

Definition element_t : Type := name_t * type_t.


(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -  *)

Section type_ind_strong.
  Variable P : type_t -> Prop.
  Hypothesis Integer_case : P Integer.
  Hypothesis Ref_case : forall (t: type_t), P t -> P (Reference t).
  Hypothesis Array_case : forall (l : nat) (t: type_t), Prop -> P t -> P (Array l t).
  Hypothesis Record_case : forall (ts: list type_t), Forall P ts -> P (Tuple ts).

  Fixpoint type_ind_strong (t : type_t) : P t :=
    match t with
    | Integer => Integer_case
    | Reference t => Ref_case t (type_ind_strong t)
    | Array l t => Array_case l t (l > 0) (type_ind_strong t)
    | Tuple ts =>
      Tuple_case ts 
        ( ( fix tuple_list_ind (ts : list type_t) : Forall P ts :=
            match ts with
            | [] => Forall_nil _
            | t :: ts' => Forall_cons t (type_ind_strong t) (tuple_list_ind ts')
            end ) 
          ts )
    end.
End type_ind_strong.


(* -------------------------------------------------------------------------- *)
(* Type Equality *)
(* -------------------------------------------------------------------------- *)


(** [Equal a b] is True if types [a] and [b] are structurally equivalent. 

  Lists of procedure parameters are equal if the parameters from each list can 
  be paired, and each pair of parameters has an equal parameter passing method 
  and type. (Parameter names are ignored, they are just placeholders.)

  Lists of record elements are equal if the elements from each list be paired,
  and each pair of elements has the an equal name and equal type. *)

Fixpoint Equal (t1: type_t) (t2: type_t) : Prop :=
  match t1, t2 with
  | Integer, Integer => True
  | Boolean, Boolean => True
  | Byte, Byte => True
  | Word, Word => True
  | Real, Real => True
  | NilReference, NilReference => True
  | Reference rt1, Reference rt2 => Equal rt1 rt2  
  | Array len1 et1, Array len2 et2 => len1 = len2 /\ Equal et1 et2
  | OpenArray et1, OpenArray et2 => Equal et1 et2
  | Record es1, Record es2 =>
    (fix equal_elements xs ys :=    (* Gallina requires this nesting :-\ *)
      match xs, ys with
      | (n1, t1) :: xs', (n2, t2) :: ys' => 
          n1 = n2 /\ Equal t1 t2 /\ equal_elements xs' ys'
      | [], [] => True
      | _, _ => False
      end
    ) es1 es2
  | Procedure ps1 rt1, Procedure ps2 rt2 =>
    Equal rt1 rt2 /\
    (fix equal_parameters xs ys :=
      match xs, ys with
      | (_, p1, t1) :: xs', (_, p2, t2) :: ys' => 
           p1 = p2 /\ Equal t1 t2 /\ equal_parameters xs' ys'
      | [], [] => True
      | _, _ => False
      end
    ) ps1 ps2
  | Statement, Statement => True
  | _, _ => False 
  end.

(*
Theorem Equal_reflexitivity : forall (t: type_t), Equal t t. 
Proof.
  intros.
  induction t; simpl.
  - apply I.
  - apply I.
  - apply I.
  - apply I.
  - apply I.
  - apply IHt. (* Reference *)
  - apply I.
  - split. (* Array *)
    + reflexivity.
    + apply IHt.
  - apply IHt. (* OpenArray *)
  - ???
*)



(* -------------------------------------------------------------------------- *)
(* Type Validity *)
(* -------------------------------------------------------------------------- *)


(** [valid_variable a] is True if type [a] can be stored in a variable, or is
  assignable.  (Vanilla's assignment operator works on atomic types and 
  equally-typed records and arrays. *)

Fixpoint valid_variable (t: type_t) : Prop :=
  match t with
  | Integer => True
  | Boolean => True
  | Byte => True
  | Word => True
  | Real => True
  | Reference rt => valid_reference rt
  | NilReference => False
  | Array len et => len >= 1 /\ valid_variable et
  | OpenArray _ => False
  | Record es =>
      length es >= 1 /\
      (fix element_test es ns :=
        match es, ns with
        | [], _ => True
        | (n, t) :: es', ns => 
            ~ In n ns /\ 
            valid_variable t /\ 
            element_test es' (n :: ns) 
        end  
      ) es []
  | Procedure _ _ => False
  | Statement => False
  end


(** [valid_reference a] is True if type [a] can be used as a reference type 
    target or a pass-by-reference procedure parameter. *)

with valid_reference (t: type_t) : Prop :=
  match t with
  | Statement => False
  | Integer => True
  | Boolean => True
  | Byte => True
  | Word => True
  | Real => True
  | Reference rt => valid_reference rt
  | NilReference => False
  | Array len et => len >= 1 /\ valid_variable et
  | OpenArray a => valid_variable a

  | Record es =>
      length es >= 1 /\
      (fix element_test es ns :=
        match es, ns with
        | [], _ => True
        | (n, t) :: es', ns => 
            ~In n ns /\ valid_variable t /\ 
            element_test es' (n :: ns) 
        end) es []

  | Procedure ps rt =>
      valid_return rt /\
      (fix parameter_test ps :=
        match ps with
        | [] => True
        | (_, ByReference, t) :: ps' => valid_reference t /\ parameter_test ps'
        | (_, ByValue, t) :: ps' => valid_parameter t /\ parameter_test ps'
        end) ps
  end


(** [valid_parameter a] is True if type [a] can be used as a value procedure 
    parameter. (Structured types are allowed. They are passed by reference, 
    but value parameters are immutuable within the called procedure.) *)

with valid_parameter (t: type_t) : Prop :=
  match t with
  | Statement => False
  | Integer => True
  | Boolean => True
  | Byte => True
  | Word => True
  | Real => True
  | Reference rt => valid_reference rt
  | NilReference => True
  | Array _ _ => False
  | OpenArray a => valid_variable a
  | Record _ => False

  | Procedure ps rt =>
      valid_return rt /\
      (fix parameter_test ps :=
        match ps with
        | [] => True
        | (_, ByReference, t) :: ps' => valid_reference t /\ parameter_test ps'
        | (_, ByValue, t) :: ps' => valid_parameter t /\ parameter_test ps'
        end) ps
  end

with valid_return (t: type_t) : Prop :=
  match t with
  | Integer => True
  | Boolean => True
  | Byte => True
  | Word => True
  | Real => True
  | Reference rt => valid_reference rt
  | NilReference => True
  | Array _ _ => False
  | OpenArray _ => False
  | Record _ => False
  | Procedure _ _ => False
  | Statement => True   (* proper procedures do not have return values *) 
  end.


(** [valid_value t] is True if type [t] is an acceptable expression value. 
    (Vanilla expressions have atomic types.) *)

Definition valid_value (t: type_t) : Prop :=
  match t with
  | Integer => True
  | Boolean => True
  | Byte => True
  | Word => True
  | Real => True
  | Reference rt => valid_reference rt
  | NilReference => True
  | Array _ _ => False
  | OpenArray _ => False
  | Record _ => False
  | Procedure _ _ => False
  | Statement => False
  end.

(* -------------------------------------------------------------------------- *)
(* Assignment Compatibilities *)
(* -------------------------------------------------------------------------- *)


(** [assignment_compatible dst src] is True if a variable of type [dst] can be
    assigned a value of type [src].

    Two types are usually assignment compatible if they have equal types.
    The exceptions are that any reference can be assigned [nil] and a reference
    to a procedure can be assigned a procedure of the correct type.
    But otherwise open arrays, procedures and statements cannot be assigned. *)


Definition assignment_compatible (dst: type_t) (src: type_t) : Prop :=
  match dst, src with
  | Reference _,  NilReference => True
  | NilReference, _            => False
  | OpenArray _,  _            => False
  | _,            OpenArray _  => False
  | t1,           t2           => Equal t1 t2
  end.


(** [var_parameter_compatible dst src] is True if a designator of type
    [src] can by supplied to a pass-by-reference procedure parameter of 
    type [dst].

    A supplied parameter is type compatible with a [var] formal parameter if
    their types are equal. The exception is that arrays are compatible with 
    open arrays if their element types are equal. *)

Definition var_parameter_compatible (dst: type_t) (src: type_t) : Prop :=
  match dst, src with
  | OpenArray et1,  Array _ et2  => Equal et1 et2
  | t1,             t2           => Equal t1 t2
  end.


(** [value_parameter_type_compatible dst src] is True if a value of type
    [src] can by supplied to a pass-by-value parameter of type [dst].

    An supplied parameter is type compatible with a value formal parameter if
    their types are assignment comatible. The exception is that arrays are 
    compatible with open arrays if their element types are equal. *)

Definition value_parameter_compatible (dst: type_t) (src: type_t) : Prop :=
  match dst, src with
  | OpenArray et1,  Array _ et2    => Equal et1 et2
  | OpenArray et1,  OpenArray et2  => Equal et1 et2
  | t1,             t2             => assignment_compatible t1 t2
  end.


(* -------------------------------------------------------------------------- *)
(* Procedure Call Validity *)
(* -------------------------------------------------------------------------- *)

(** [ValidProcedureCall] is true if: there are the same number of supplied 
    call parameters as procedure parameters; pass-by-reference parameters are 
    supplied designators, not values; and the types of each pair of procedure 
    parameter and supplied parameter are compatible. *)

Inductive call_parameter_t : Type :=
  | SuppliedValue (value: type_t)
  | SuppliedDesignator (designator: type_t).


Definition CompatibleParameter (ps: parameter_t * call_parameter_t) : Prop :=
  match ps with
  | ((_, ByValue, pt), SuppliedValue st) => value_parameter_compatible pt st 
  | ((_, ByValue, pt), SuppliedDesignator st) =>  value_parameter_compatible pt st
  | ((_, ByReference, pt), SuppliedDesignator st) => var_parameter_compatible pt st
  | (_,  _) => False
  end.

Definition ValidProcedureCall
    (parameters: list parameter_t)
    (supplied: list call_parameter_t) : Prop :=
  length parameters = length supplied /\ 
  Forall CompatibleParameter (combine parameters supplied). 

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)

Theorem ValidProcedureCall_no_parameters : ValidProcedureCall [] [].
Proof.
  unfold ValidProcedureCall. simpl. 
  split.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma ValidProcedureCall_wrong_number_of_parameters : 
  forall (pp: list parameter_t) (sp: list call_parameter_t),
  length sp <> length pp -> ~ValidProcedureCall pp sp.
Proof.
  intros pp ss Length.
  intros Valid. apply Length. (* contrapositive *)
  unfold ValidProcedureCall in Valid.
  destruct Valid as [ValidLength _]. 
  rewrite ValidLength.
  reflexivity.
Qed.
