Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Section type_t.

  Unset Elimination Schemes.

  Inductive passing_method_t :=
    | ByReference
    | ByValue.

  Inductive type_t : Type :=
    | Statement : type_t
    | Nil       : type_t
    | Integer   : type_t
    | Reference : type_t -> type_t
    | Record    : list (string * type_t) -> type_t
    | Procedure : list (passing_method_t * type_t) -> type_t -> type_t. 

  Set Elimination Schemes.

  Section type_t_ind.

    Variables 
      (P : type_t -> Prop)
      (HStatement : 
        P Statement)
      (HNil : 
        P Nil)
      (HInteger : 
        P Integer)
      (HReference : 
        forall targettype, P targettype -> P (Reference targettype))
      (HRecord : 
        forall elements, 
        (forall name type, In (name, type) elements -> P type) -> 
        P (Record elements))
      (HProcedure : 
        forall args returntype, 
        (forall pass type, In (pass, type) args -> P type) -> 
        P returntype -> 
        P (Procedure args returntype)).

    Fixpoint type_t_ind type : P type.
    Proof.
      destruct type as [ | | | | elements | args returntype ].
      + apply HStatement.
      + apply HNil.
      + apply HInteger.
      + apply HReference. 
        apply type_t_ind.
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
    Qed.

  End type_t_ind.


  Let sub_type_t s t :=
    (* True if type "s" a component of structured type "t" *)
    match t with
    | Statement => False
    | Nil => False
    | Integer => False
    | Reference r => r = s
    | Record elements => exists name, In (name, s) elements
    | Procedure args rtype => exists pass, In (pass, s) args \/ s = rtype
    end.

  Local Fact wf_sub_type : well_founded sub_type_t.
  Proof. 
    intros t.
    induction t; constructor; intros ? [].
    - intuition.    (* Reference *)
    - eauto.        (* Record *)
    - destruct H0.  (* Procedure *)
      + apply H with (pass := x)(type := y). apply H0. (* args *)
      + subst. apply IHt.                              (* return type *)
  Qed.


  Section type_t_rect.

    Variables 
      (P : type_t -> Prop)
      (HStatement : 
        P Statement)
      (HNil : 
        P Nil)
      (HInteger : 
        P Integer)
      (HReference : 
        forall targettype, P targettype -> P (Reference targettype))
      (HRecord : 
        forall elements, 
        (forall name type, In (name, type) elements -> P type) -> 
        P (Record elements))
      (HProcedure : 
        forall args returntype, 
        (forall pass type, In (pass, type) args -> P type) -> 
        P returntype -> 
        P (Procedure args returntype)).

    Theorem type_t_rect type : P type.
    Proof.
      induction type as [ [ | | | r | l | l r] IH ] 
          using (well_founded_induction_type wf_sub_type).
      + apply HStatement.
      + apply HNil.
      + apply HInteger.
      + apply HReference. apply IH. constructor.
      + apply HRecord.
        intros name ? ?. apply IH. now exists name.
      + apply HProcedure.
        - intros pass ? ?. apply IH. exists pass. left. apply H.
        - apply IH. exists ByValue. right. reflexivity.
    Qed.

  End type_t_rect.


  Definition type_t_rec (P : _ -> Prop) := type_t_rect P.


  Variable string_equal : string -> string -> Prop.
  Variable passing_equal : passing_method_t -> passing_method_t -> Prop.

  Inductive TypeEqual : type_t -> type_t -> Prop :=
    | TypeEqual_Statement : 
        TypeEqual Statement Statement
    | TypeEqual_Nil : 
        TypeEqual Nil Nil
    | TypeEqual_Integer : 
        TypeEqual Integer Integer
    | TypeEqual_Reference t  :  
        TypeEqual (Reference t) (Reference t)
    | TypeEqual_Record elements1 elements2 : 
        Forall2 string_equal (map fst elements1) (map fst elements2) -> 
        Forall2 TypeEqual (map snd elements1) (map snd elements2) -> 
        TypeEqual (Record elements1) (Record elements2)
    | TypeEqual_Procedure args1 rettype1 args2 rettype2 : 
        Forall2 passing_equal (map fst args1) (map fst args2) ->  
        Forall2 TypeEqual (map snd args1) (map snd args2) -> 
        TypeEqual rettype1 rettype2 ->
        TypeEqual (Procedure args1 rettype1) (Procedure args2 rettype2)
    .

  Fact Forall2_refl X R l : 
    (forall x : X, In x l -> R x x) -> Forall2 R l l.
  Proof.
    rewrite <- Forall_forall.
    induction 1; auto.
  Qed.

  Hypothesis string_equal_refl : forall x : string, string_equal x x.
  Hypothesis passing_equal_refl : forall x : passing_method_t, passing_equal x x.

  Fact TypeEqual_refl (t: type_t) : TypeEqual t t.
  Proof.
    induction t; constructor; try apply Forall2_refl.  
    (* Records *)
    + intros. apply string_equal_refl.  
    + intros ? ((name, type) & <- & ?)%in_map_iff. eauto.
    (* Procedures. *)
    + intros. apply passing_equal_refl.
    + intros ? ((pass, type) & <- & ?)%in_map_iff. eauto.
    + apply IHt.
  Qed.

End type_t.
