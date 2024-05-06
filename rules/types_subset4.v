Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition name_t := string.

Section type_t.

  Inductive passing_method_t :=
    | ByReference
    | ByValue.

  Unset Elimination Schemes.

  Inductive type_t : Type :=
    | Statement : type_t
    | Nil       : type_t
    | Integer   : type_t
    | Reference : type_t -> type_t
    | OpenArray : type_t -> type_t
    | Array     : nat -> type_t -> type_t
    | Record    : list (name_t * type_t) -> type_t
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
        P (Procedure args rtype)).

    Fixpoint type_t_ind type : P type.
    Proof.
      destruct type as [ | | | dtype | etype | len etype | elements | args rtype ].
      + apply HStatement.
      + apply HNil.
      + apply HInteger.
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
    Qed.

  End type_t_ind.


  Let sub_type_t s t :=
    (* True if type "s" a component of structured type "t" *)
    match t with
    | Statement => False
    | Nil => False
    | Integer => False
    | Reference dtype => dtype = s
    | OpenArray etype => etype = s
    | Array _ etype => etype = s
    | Record elements => exists name, In (name, s) elements
    | Procedure args rtype => exists pass, In (pass, s) args \/ s = rtype
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
      (HStatement : 
        P Statement)
      (HNil : 
        P Nil)
      (HInteger : 
        P Integer)
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
        P (Procedure args rtype)).

    Theorem type_t_rect type : P type.
    Proof.
      induction type as [ [ | | | dtype | etype | len etype | elts | args rtype ] IH ] 
          using (well_founded_induction_type wf_sub_type).
      + apply HStatement.
      + apply HNil.
      + apply HInteger.
      + apply HReference. apply IH. constructor.
      + apply HOpenArray. apply IH. constructor.
      + apply HArray. apply IH. constructor.
      + apply HRecord.
        intros name ? ?. apply IH. now exists name.
      + apply HProcedure.
        - intros pass ? ?. apply IH. exists pass. left. apply H.
        - apply IH. exists ByValue. right. reflexivity.
    Qed.

  End type_t_rect.


  Definition type_t_rec (P : _ -> Prop) := type_t_rect P.

  Inductive TypeEqual : type_t -> type_t -> Prop :=
    | TypeEqual_Statement : 
        TypeEqual Statement Statement
    | TypeEqual_Nil : 
        TypeEqual Nil Nil
    | TypeEqual_Integer : 
        TypeEqual Integer Integer
    | TypeEqual_Reference t  :  
        TypeEqual (Reference t) (Reference t)
    | TypeEqual_OpenArray t  :  
        TypeEqual (OpenArray t) (OpenArray t)
    | TypeEqual_Array len t :  
        TypeEqual (Array len t) (Array len t)

    | TypeEqual_Record elements1 elements2 : 
        Forall2 eq (map fst elements1) (map fst elements2) -> 
        Forall2 TypeEqual (map snd elements1) (map snd elements2) -> 
        TypeEqual (Record elements1) (Record elements2)
    
    | TypeEqual_Procedure args1 rettype1 args2 rettype2 : 
        Forall2 eq (map fst args1) (map fst args2) ->  
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


  Fact TypeEqual_refl (t: type_t) : TypeEqual t t.
  Proof.
    induction t; constructor; try apply Forall2_refl.
    + intros. reflexivity.                                 (* Record names *)
    + intros ? ((name, type) & <- & HI)%in_map_iff. eauto. (* Record types *)
    + intros. reflexivity.                                 (* Procedure passing *)
    + intros ? ((pass, type) & <- & HI)%in_map_iff. eauto. (* Procedure args. *)
    + apply IHt.                                           (* Procedure return. *)
  Qed.

End type_t.
