Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Coq.Logic.Decidable.
Import ListNotations.

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
  Variable module_equivalent : module_t -> type_t -> type_t -> Prop.

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
  | t => special_type t
  end.

  Definition value_type (t: type_t) : Prop := atomic_type t \/ t = Nil.
  
  Definition return_type (t: type_t) : Prop := atomic_type t \/ t = Statement.
  
  Definition referenceable_type  (t: type_t) : Prop := ~(special_type t).

  Definition value_parameter_type (t: type_t) : Prop := 
    referenceable_type t \/ value_type t.


  (* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)

  Theorem atomic_and_structured_are_distinct : forall (t: type_t),
    ~ (atomic_type t /\ structured_type t).
  Proof.
    intros. unfold not. intros. destruct H as [Ha Hs].
    destruct t; simpl in *; try destruct Ha; try destruct Hs. 
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
    ~ (sized_type t /\ unsized_type t).
  Proof.
    intros. unfold not. intros.
    destruct H as [Hs Hu].
    inversion t; simpl in *; try destruct Hs; try destruct Hu. 
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
(* Type Validity *)
(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)

Inductive valid_type : type_t -> Prop :=
  | valid_type_Statement : valid_type Statement
  | valid_type_Nil :       valid_type Nil
  | valid_type_Boolean :   valid_type Boolean
  | valid_type_Integer :   valid_type Integer
  | valid_type_Byte :      valid_type Byte
  | valid_type_Word :      valid_type Word
  | valid_type_Real :      valid_type Real
  | valid_type_Reference t : 
      sized_type t -> 
      valid_type t -> 
      valid_type (Reference t)
  | valid_type_OpenArray t : 
      valid_type t -> 
      sized_type t -> 
      valid_type (OpenArray t)
  | valid_type_Array len t : 
      len > 0 -> 
      valid_type t -> 
      sized_type t -> 
      valid_type (Array len t)
  | valid_type_Record elements :
      NoDup (map fst elements) ->
      Forall sized_type (map snd elements) -> 
      Forall valid_type (map snd elements) -> 
      valid_type (Record elements) 
  | valid_type_Procedure args rettype : 
      valid_type rettype -> 
      return_type rettype ->
      Forall valid_type (map snd args) -> 
      Forall (fun a => fst a = ByValue -> value_parameter_type (snd a)) args ->
      Forall (fun a => fst a = ByReference -> reference_type (snd a)) args ->
      valid_type (Procedure args rettype)
  | valid_type_NamedRef name : 
      valid_type (NamedRef name)    (* XXX *) 
  | valid_type_Abstract name : 
      valid_type (Abstract name).   (* XXX *)

End rules.
