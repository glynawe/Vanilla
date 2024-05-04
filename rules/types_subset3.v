Require Import Coq.Lists.List.
Import ListNotations.
Require Coq.Strings.String.


(*---------------------------------------------------------------------------*)
(* Types *)
(*---------------------------------------------------------------------------*)


Definition name_t := Coq.Strings.String.string.

Inductive passing_t : Type := ByValue | ByReference.

Inductive type_t : Type :=
  | Integer
  | Ref (referenced: type_t)
  | Array (length: nat) (element: type_t)
  | OpenArray (element: type_t)
  | Record (names: list name_t) (types: list type_t)
  | Procedure (names: list name_t) (methods: list passing_t) (types: list type_t).

Section type_ind_strong.
  Variable P : type_t -> Prop.
  Hypothesis Integer_case : P Integer.
  Hypothesis Ref_case : forall (t: type_t), P t -> P (Ref t).
  Hypothesis Array_case : forall (l : nat) (t: type_t), P t -> P (Array l t).
  Hypothesis OpenArray_case : forall (t: type_t), P t -> P (OpenArray t).
  Hypothesis Record_case : 
    forall (ns: list name_t) (ts: list type_t), 
    Forall P ts -> P (Record ns ts).
  Hypothesis Procedure_case : 
    forall (ns: list name_t) (ps: list passing_t) (ts: list type_t), 
    Forall P ts -> P (Procedure ns ps ts).

  Fixpoint type_ind_strong (t : type_t) : P t :=
    match t with
    | Integer => Integer_case
    | Ref t => Ref_case t (type_ind_strong t)
    | Array l t => Array_case l t (type_ind_strong t)
    | OpenArray t => OpenArray_case t (type_ind_strong t)
    | Record ns ts =>
      Record_case ns ts
        ( ( fix type_list_ind (ts : list type_t) : Forall P ts :=
            match ts with
            | t :: ts' => Forall_cons t (type_ind_strong t) (type_list_ind ts')
            | [] => Forall_nil _
            end )
          ts )
    | Procedure ns ps ts =>
      Procedure_case ns ps ts
        ( ( fix type_list_ind (ts : list type_t) : Forall P ts :=
            match ts with
            | t :: ts' => Forall_cons t (type_ind_strong t) (type_list_ind ts')
            | [] => Forall_nil _
            end )
          ts )
    end.
End type_ind_strong.


(*---------------------------------------------------------------------------*)
(* Type equality *)
(*---------------------------------------------------------------------------*)

Fixpoint Equal (t1: type_t) (t2: type_t) : Prop :=
  match t1, t2 with
  | Integer, Integer => True
  | Ref rt1, Ref rt2 => Equal rt1 rt2  
  | Array len1 et1, Array len2 et2 => len1 = len2 /\ Equal et1 et2
  | OpenArray et1, OpenArray et2 => Equal et1 et2
  | Record ns1 ts1, Record ns2 ts2 =>
    ns1 = ns2 /\
    (fix equal_elements xs ys :=
      match xs, ys with
      | t1 :: xs', 
        t2 :: ys' => Equal t1 t2 /\ equal_elements xs' ys'
      | nil, nil => True
      | _, _ => False
      end
    ) ts1 ts2
  | Procedure ns1 ps1 ts1, Procedure ns2 ps2 ts2 =>
    ns1 = ns2 /\
    ps1 = ps2 /\
    (fix equal_elements xs ys :=
      match xs, ys with
      | t1 :: xs', 
        t2 :: ys' => Equal t1 t2 /\ equal_elements xs' ys'
      | nil, nil => True
      | _, _ => False
      end
    ) ts1 ts2
  | _, _ => False 
  end.

Theorem Equal_reflexivity : forall (t: type_t), Equal t t.
Proof.
  induction t using type_ind_strong; simpl; auto.
  - induction H; simpl; auto; split; auto. (* Record *)
    destruct IHForall; auto.
  - induction H; simpl; auto. (* Procedure *)
    destruct IHForall as [H1 H2]. destruct H2. split; auto.
Qed.


(*---------------------------------------------------------------------------*)
(* Type validity *)
(*---------------------------------------------------------------------------*)

Fixpoint Valid (t: type_t)  : Prop :=
  match t with
  | Ref rt => Valid rt
  | Array l et => l > 0 /\ Valid et
  | Record ns ts => 
      length ns = length ts /\
      NoDup ns /\
      (fix valid_types ts :=
        match ts with
        | [] => True
        | t :: ts' => Valid t /\  valid_types ts' 
        end) ts
  | Procedure ns ps ts => 
      length ns = length ts /\
      length ps = length ts /\
      (fix valid_types ts :=
        match ts with
        | [] => True
        | t :: ts' => Valid t /\  valid_types ts' 
        end) ts
  | _ => True
  end.
