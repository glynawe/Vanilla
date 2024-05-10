Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Coq.Logic.Decidable.
Import ListNotations.

Lemma Forall2_refl X R l : 
  (forall x : X, In x l -> R x x) -> Forall2 R l l.
Proof.
  rewrite <- Forall_forall.
  induction 1; auto.
Qed.


Definition name_t := string.

Definition globalname_t := string.

Section type_t.

  Inductive passing_method_t :=
    | ByReference
    | ByValue.

  Unset Elimination Schemes.

  Inductive type_t : Type :=
    | Statement : type_t
    | Nil       : type_t
    | Boolean   : type_t
    | Integer   : type_t
    | Byte      : type_t
    | Word      : type_t
    | Real      : type_t
    | Reference : type_t -> type_t
    | OpenArray : type_t -> type_t
    | Array     : nat -> type_t -> type_t
    | Record    : list (name_t * type_t) -> type_t
    | Procedure : list (passing_method_t * type_t) -> type_t -> type_t
    | NamedRef  : globalname_t -> type_t 
    | Abstract  : globalname_t -> type_t.

  Set Elimination Schemes.

  Section type_t_ind.

    Variables 
      (P : type_t -> Prop)
      (HStatement : P Statement)
      (HBoolean :   P Boolean)
      (HNil :       P Nil)
      (HInteger :   P Integer)
      (HByte :      P Byte)
      (HWord :      P Word)
      (HReal :      P Real)
      (HReference : 
        forall dtype, P dtype -> P (Reference dtype))
      (HOpenArray : 
        forall etype, P etype -> P (OpenArray etype))
      (HArray : 
        forall len etype, P etype -> P (Array len etype))
      (HRecord : 
        forall elements, 
        (forall name type, In (name, type) elements -> P type) -> 
        P (Record elements))
      (HProcedure : 
        forall args rtype, 
        (forall pass type, In (pass, type) args -> P type) -> 
        P rtype -> 
        P (Procedure args rtype))
      (HNamedRef : 
        forall name, P (NamedRef name))
      (HAbstract :
        forall name, P (Abstract name)).

    Fixpoint type_t_ind type : P type.
    Proof.
      destruct type as [ | | | | | | | dtype | etype | len etype
                       | elements | args rtype | name | name ].
      + apply HStatement.
      + apply HNil.
      + apply HBoolean.
      + apply HInteger.
      + apply HByte.
      + apply HWord.
      + apply HReal.
      + apply HReference. apply type_t_ind.
      + apply HOpenArray. apply type_t_ind.
      + apply HArray. apply type_t_ind.
      + apply HRecord.
        induction elements as [ | elt elements IH ].
        * intros _ _ [].
        * intros name type [ E | H ].
          - specialize (type_t_ind (snd elt)); now subst.
          - apply IH with (1 := H).
      + apply HProcedure.
        induction args as [ | arg args IH ].
        * intros _ _  [].
        * intros pass type [ E | H ].
          - specialize (type_t_ind (snd arg)); now subst.
          - apply IH with (1 := H).
        * apply type_t_ind.
      + apply HNamedRef.
      + apply HAbstract.
    Qed.

  End type_t_ind.


  Let sub_type_t s t :=
    (* True if type "s" a component of structured type "t" *)
    match t with
    | Statement => False
    | Nil => False
    | Boolean => False
    | Integer => False
    | Byte => False
    | Word => False
    | Real => False
    | Reference dtype => dtype = s
    | OpenArray etype => etype = s
    | Array _ etype => etype = s
    | Record elements => exists name, In (name, s) elements
    | Procedure args rtype => exists pass, In (pass, s) args \/ s = rtype
    | NamedRef _ => False
    | Abstract _ => False
    end.

  Local Fact wf_sub_type : well_founded sub_type_t.
  Proof. 
    intros t.
    induction t; constructor; intros ? [].
    - apply IHt.
    - apply IHt.
    - apply IHt.
    - apply H with (name := x)(type := y). apply H0.  (* Record *) 
    - destruct H0.                                    (* Procedure *)
      + apply H with (pass := x)(type := y). apply H0.  (* args *)
      + rewrite <- H0 in IHt. apply IHt.                (* rtype *)
  Qed.

  Section type_t_rect.

    Variables 
      (P : type_t -> Prop)
      (HStatement : P Statement)
      (HBoolean :   P Boolean)
      (HNil :       P Nil)
      (HInteger :   P Integer)
      (HByte :      P Byte)
      (HWord :      P Word)
      (HReal :      P Real)
      (HReference : 
        forall dtype, P dtype -> P (Reference dtype))
      (HOpenArray : 
        forall etype, P etype -> P (OpenArray etype))
      (HArray : 
        forall len etype, P etype -> P (Array len etype))
      (HRecord : 
        forall elements, 
        (forall name type, In (name, type) elements -> P type) -> 
        P (Record elements))
      (HProcedure : 
        forall args rtype, 
        (forall pass type, In (pass, type) args -> P type) -> 
        P rtype -> 
        P (Procedure args rtype))
      (HNamedRef : 
        forall name, P (NamedRef name))
      (HAbstract :
        forall name, P (Abstract name)).

    Theorem type_t_rect type : P type.
    Proof.
      induction type as [ [ | | | | | | | dtype | etype | len etype 
                          | elements | args rtype | name | name ] IH ] 
          using (well_founded_induction_type wf_sub_type).
      + apply HStatement.
      + apply HNil.
      + apply HBoolean.
      + apply HInteger.
      + apply HByte.
      + apply HWord.
      + apply HReal.
      + apply HReference. apply IH. constructor.
      + apply HOpenArray. apply IH. constructor.
      + apply HArray. apply IH. constructor.
      + apply HRecord.
        intros name ? ?. apply IH. now exists name.
      + apply HProcedure.
        - intros pass ? ?. apply IH. exists pass. left. apply H.
        - apply IH. exists ByValue. right. reflexivity.
      + apply HNamedRef.
      + apply HAbstract.
    Qed.

  End type_t_rect.

  Definition type_t_rec (P : _ -> Prop) := type_t_rect P.

End type_t.


Module rules.
  Variable module_t : Type.
  Variable module_get_type : module_t -> globalname_t -> type_t -> Prop.
  Variable module_equivalent : module_t -> globalname_t -> globalname_t -> Prop.
  Hypothesis module_equivalent_refl : forall m n, module_equivalent m n n.
  
  Definition atomic_type (t: type_t) : Prop := 
  match t with
  | Boolean   => True
  | Integer   => True
  | Byte      => True
  | Word      => True
  | Real      => True
  | Reference _ => True
  | NamedRef _ => True
  | _ => False
  end. 

  Definition structured_type (t: type_t) : Prop :=  
  match t with
  | OpenArray _ => True
  | Array _ _ => True
  | Record _ => True
  | Procedure _ _ => True
  | Abstract _ => True
  | _ => False
  end.

  Definition special_type (t: type_t) : Prop :=  
  match t with
  | Nil => True
  | Statement => True
  | _ => False
  end.

  Definition reference_type (t: type_t) : Prop :=  
  match t with
  | Nil => True 
  | Reference _ => True
  | NamedRef _ => True
  | _ => False
  end.

  Definition unsized_type (t: type_t) : Prop :=  
  match t with
  | OpenArray _ => True 
  | Abstract _ => True
  | Statement => True
  | _ => False
  end.

  Definition value_type (t: type_t) : Prop := atomic_type t \/ t = Nil.
  
  Definition return_type (t: type_t) : Prop := atomic_type t \/ t = Statement.
  
  Definition referenceable_type  (t: type_t) : Prop := ~(special_type t).

  Definition value_parameter_type (t: type_t) : Prop := 
    referenceable_type t \/ value_type t.

  Definition procedure_type (t: type_t) : Prop :=
    match t with Procedure _ _ => True | _ => False end. 

  (* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)

  Theorem atomic_and_structured_are_distinct : forall (t: type_t),
    ~ (atomic_type t /\ structured_type t).
  Proof.
    intros. unfold not. 
    apply not_and_iff. 
    intros.
    destruct t; try destruct H; try destruct H0. 
  Qed.

  Theorem special_and_structured_are_distinct : forall (t: type_t),
    ~ (special_type t /\ structured_type t).
  Proof.
    intros. unfold not. intros. destruct H as [Ha Hs].
    destruct t; simpl in *; try destruct Ha; try destruct Hs. 
  Qed.

  Theorem special_and_atomic_are_distinct : forall (t: type_t),
    ~ (special_type t /\ atomic_type t).
  Proof.
    intros. unfold not. intros. destruct H as [Ha Hs].
    destruct t; simpl in *; try destruct Ha; try destruct Hs. 
  Qed.

  Theorem atomic_types_are_values : forall (t: type_t),
    atomic_type t -> value_type t.
  Proof.
    intros. unfold value_type. left. apply H.
  Qed.

  Theorem return_types_are_atomic : forall (t: type_t),
    atomic_type t -> return_type t.
  Proof.
    intros. unfold return_type. left. apply H.
  Qed.

  (* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)

  Inductive sized_type : type_t -> Prop :=
    | sized_type_Boolean :       sized_type Boolean
    | sized_type_Integer :       sized_type Integer
    | sized_type_Byte :          sized_type Byte
    | sized_type_Word :          sized_type Word
    | sized_type_Real :          sized_type Real
    | sized_type_Reference t :   sized_type (Reference t)
    | sized_type_NamedRef name : sized_type (NamedRef name)
    | sized_type_Array len t : 
        len > 0 -> sized_type t -> sized_type (Array len t)
    | sized_type_Record elements : 
        Forall sized_type (map snd elements) -> sized_type (Record elements). 

  (* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)

  Theorem sized_and_unsized_are_distinct : forall (t: type_t),
    sized_type t -> ~(unsized_type t).
  Proof.
    intros. unfold not. intros.
    induction t; try inversion H; try inversion H0.
  Qed.

  Theorem sized_arrays_have_sized_elements : forall (n: nat) (t: type_t),
    n > 0 -> sized_type (Array n t) -> sized_type t.
  Proof.
    intros n t H.
    intros. inversion H0. apply H4.
  Qed.

  Theorem sized_records_have_sized_elements : 
    forall (elements: list (name_t * type_t)),
    sized_type (Record elements) -> Forall sized_type (map snd elements).
  Proof.
    intros.
    inversion H. apply H1.
  Qed.

  Theorem sized_types_are_referenceable : forall (t: type_t),
    sized_type t -> referenceable_type t.    
  Proof.
    intros. inversion H; subst; unfold referenceable_type; auto.
  Qed.


(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)
(* Type Equivalence *)
(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)

  Inductive eq_types : module_t -> type_t -> type_t -> Prop :=
    | eq_types_Statement m : eq_types m Statement Statement
    | eq_types_Nil m :       eq_types m Nil Nil
    | eq_types_Boolean m :   eq_types m Boolean Boolean
    | eq_types_Integer m :   eq_types m Integer Integer
    | eq_types_Byte m :      eq_types m Byte Byte
    | eq_types_Word m :      eq_types m Word Word
    | eq_types_Real m :      eq_types m Real Real
    | eq_types_Reference m t u :
        eq_types m t u ->  
        eq_types m (Reference t) (Reference t)
    | eq_types_OpenArray m t :  
        eq_types m (OpenArray t) (OpenArray t)
    | eq_types_Array len m t :  
        eq_types m (Array len t) (Array len t)
    | eq_types_Record m elements1 elements2 : 
        Forall2 eq (map fst elements1) (map fst elements2) -> 
        Forall2 (eq_types m) (map snd elements1) (map snd elements2) -> 
        eq_types m (Record elements1) (Record elements2)
    | eq_types_Procedure m args1 rtype1 args2 rtype2 : 
        Forall2 eq (map fst args1) (map fst args2) ->  
        Forall2 (eq_types m) (map snd args1) (map snd args2) -> 
        eq_types m rtype1 rtype2 ->
        eq_types m (Procedure args1 rtype1) (Procedure args2 rtype2)
    | eq_types_NamedRef m n1 n2 :
        module_equivalent m n1 n2 -> eq_types m (NamedRef n1) (NamedRef n2)
    | eq_types_Abstract m n1 n2 :
        module_equivalent m n1 n2 -> eq_types m (Abstract n1) (Abstract n2).

  Fact eq_types_refl (m: module_t) (t: type_t) : eq_types m t t.
  Proof.
    induction t; try constructor.
    + apply (eq_types_Reference m t t). apply IHt.
    + apply Forall2_refl. intros. reflexivity.
    + apply Forall2_refl. intros ? ((name, type) & <- & ?)%in_map_iff. eauto.
    + apply Forall2_refl. intros. reflexivity.
    + apply Forall2_refl. intros ? ((name, type) & <- & ?)%in_map_iff. eauto.
    + apply IHt.
    + apply module_equivalent_refl.
    + apply module_equivalent_refl.
  Qed.


(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)
(* Type Validity *)
(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)

Inductive valid_type : module_t -> type_t -> Prop :=
  | valid_type_Statement m : valid_type m Statement
  | valid_type_Nil m :       valid_type m Nil
  | valid_type_Boolean m :   valid_type m Boolean
  | valid_type_Integer m :   valid_type m Integer
  | valid_type_Byte m :      valid_type m Byte
  | valid_type_Word m :      valid_type m Word
  | valid_type_Real m :      valid_type m Real
  | valid_type_Reference m t : 
      sized_type t -> 
      valid_type m t -> 
      valid_type m (Reference t)
  | valid_type_OpenArray m t : 
      valid_type m t -> 
      sized_type t -> 
      valid_type m (OpenArray t)
  | valid_type_Array m len t : 
      len > 0 -> 
      valid_type m t -> 
      sized_type t -> 
      valid_type m (Array len t)
  | valid_type_Record m elements :
      NoDup (map fst elements) ->
      Forall sized_type (map snd elements) -> 
      Forall (valid_type m) (map snd elements) -> 
      valid_type m (Record elements) 
  | valid_type_Procedure m args rtype : 
      valid_type m rtype -> 
      return_type rtype ->
      Forall (valid_type m) (map snd args) -> 
      Forall (fun a => fst a = ByValue -> value_parameter_type (snd a)) args ->
      Forall (fun a => fst a = ByReference -> reference_type (snd a)) args ->
      valid_type m (Procedure args rtype)
  | valid_type_NamedRef m name : 
      valid_type m (NamedRef name)    (* XXX *) 
  | valid_type_Abstract m name : 
      valid_type m (Abstract name).   (* XXX *)


(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)
(* Assignment Compatibility *)
(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)


(** [assignment_compatible m dst src] is true if a variable of type [dst] can be
    assigned a value of type [src].

    Two types are assignment compatible if they are sized and have equal types.
    In addition, any reference can be assigned [nil] and a reference
    to a procedure can be assigned a procedure of the correct type. *)

Definition equal_parameters (m: module_t) (a b: passing_method_t * type_t) : Prop :=
  fst a = fst b /\ eq_types m (snd a) (snd b).

Definition equal_procedures (m: module_t) (a b: passing_method_t * type_t) : Prop :=
  fst a = fst b /\ eq_types m (snd a) (snd b).

Definition assignment_compatible (m: module_t) (dst src: type_t) : Prop :=
  (sized_type dst /\ sized_type src) \/ 
  (reference_type dst /\ src = Nil) \/
  match dst, src with
  | Reference (Procedure dp dr), Procedure sp sr =>
      Forall2 (equal_parameters m) dp sp /\ eq_types m dr sr  
  | _, _ => False
  end.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)

Theorem nil_is_assignment_compatible : forall (m: module_t) (t: type_t),
  reference_type t -> assignment_compatible m t Nil.
Proof.
  intros. induction t; unfold assignment_compatible; auto.
Qed.

Theorem sized_are_assignment_compatible : forall (m: module_t) (t: type_t),
  sized_type t -> assignment_compatible m t t.
Proof.
  intros. induction t; unfold assignment_compatible; auto.
Qed.

Theorem procedures_are_assignment_compatible_with_refs : 
  forall (m: module_t) (args: list (passing_method_t * type_t)) (rtype: type_t),
  assignment_compatible m (Reference (Procedure args rtype)) (Procedure args rtype).
Proof.
  intros.
  unfold assignment_compatible. right. right.
  split.
  + apply Forall2_refl. unfold equal_parameters. intuition. apply eq_types_refl.
  + apply eq_types_refl.
Qed.

(*
Theorem unsized_cannot_be_assigned : forall (m: module_t) (t u: type_t),
  unsized_type u -> ~(assignment_compatible m t u).
*)

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)
(* Procedure Parameter Compatibility *)
(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)


(** [reference_parameter_compatible m dst src] is true if a designator of type
    [src] can by passed by reference to a procedure parameter of type [dst].

    The supplied parameter an procedure parameter must have equal types. 
    The exception is that arrays are compatible with open arrays if their 
    element types are equal. *)

Definition reference_parameter_compatible (m: module_t) (dst src: type_t) : Prop :=
  match dst, src with
  | OpenArray t1, Array _ t2 => eq_types m t1 t2
  | OpenArray t1, OpenArray t2 => eq_types m t1 t2
  | t1, t2 => eq_types m t1 t2
  end.

(** [value_parameter_compatible m dst src] is true if a designator of type
    [src] can by passed by value to a procedure parameter of type [dst].

    The supplied parameter must be assignment compatible with the procedure 
    parameter. The exception is that arrays are compatible with open arrays 
    if their element types are equal m. *)

Definition value_parameter_compatible (m: module_t) (dst src: type_t) : Prop :=
  reference_parameter_compatible m dst src \/
  assignment_compatible m dst src.


End rules.
