
(* Type system with a recursively defined Tuple type. It is "nested
  recursion" because there is an intervening type: type_t recurs 
  inside a list. *)

(* This shows how to create recursive functions over types with nested 
  recursion and an induction principle to handle proofs for the type. *)
 
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope bool_scope.

Inductive type_t : Type :=
  | Integer
  | Ref (rt: type_t)
  | Array (length: nat) (element: type_t)
  | Tuple (elements: list type_t).

Fixpoint Equal (t1: type_t) (t2: type_t) : Prop :=
  match t1, t2 with
  | Integer, Integer => True
  | Ref rt1, Ref rt2 => Equal rt1 rt2  
  | Array len1 et1, Array len2 et2 => len1 = len2 /\ Equal et1 et2
  (* | Tuple es1, Tuple es2 => Forall2 Equal es1 es2 *)
  | Tuple es1, Tuple es2 =>
    (fix equal_elements xs ys :=   (* this must be done instead *)
      match xs, ys with
      | t1 :: xs', t2 :: ys' => Equal t1 t2 /\ equal_elements xs' ys'
      | nil, nil => True
      | _, _ => False
      end
    ) es1 es2
  | _, _ => False 
  end.

Section type_ind_strong.
  Variable P : type_t -> Prop.
  Hypothesis Integer_case : P Integer.
  Hypothesis Ref_case : forall (t: type_t), P t -> P (Ref t).
  Hypothesis Array_case : forall (l : nat) (t: type_t), Prop -> P t -> P (Array l t).
  Hypothesis Tuple_case : forall (ts: list type_t), Forall P ts -> P (Tuple ts).

  Fixpoint type_ind_strong (t : type_t) : P t :=
    match t with
    | Integer => Integer_case
    | Ref t => Ref_case t (type_ind_strong t)
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

Theorem Equal_refl : forall (t: type_t), Equal t t.
Proof.
  induction t using type_ind_strong; simpl; auto.
  induction H; auto.
Qed.

(*
Theorem Equal_refl : forall (t: type_t), Equal t t.
Proof.
  intros.
  induction t using type_ind_strong; simpl.
  - reflexivity.
  - apply IHt.
  - split. reflexivity. apply IHt.
  - induction H.
    + reflexivity.
    + split.
      * apply H.
      * apply IHForall.
Qed.
*)  
