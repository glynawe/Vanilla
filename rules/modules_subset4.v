Require Import Coq.Strings.String.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.Equalities.
Require Import Coq.FSets.FMapWeakList.
Require Import Coq.Lists.List.
Require Import Coq.Structures.OrderedTypeEx.
Import ListNotations.
From MMaps Require Import MMaps.  (* opam install coq-mmaps *)


Lemma same_either_way : forall {T: Type} (c: bool) (a: T),
  (if c then a else a) = a.
Proof.
  intros. destruct c; reflexivity.
Qed.

Definition some_if {T: Type} (x: T) (c: bool) : option T :=
  if c then Some x else None.

Lemma some_if_true : forall {T: Type} (x: T) (c: bool),
  some_if x c = Some x <-> c = true.
Proof.
  split. 
  + intros. unfold some_if in H. destruct c. 
    - intuition. 
    - discriminate.
  + intros. unfold some_if. destruct c.
    - intuition.
    - discriminate.
Qed. 

Lemma match_true : forall {T: Type} (x: T) (c: bool),

match c = true with
| Some x => definition_eqb dm d
| None => false
end = true

(* ------------------------------------------------------------------------- *)
(* see https://pdp7.org/blog/2011/01/the-maybe-monad-in-coq/ *)

Definition ret {A : Type} (x : A) := Some x.

Definition bind {A B : Type} (a : option A) (f : A -> option B) : option B :=
  match a with
    | Some x => f x
    | None => None
  end.

Notation "A >>= F" := (bind A F) (at level 42, left associativity).

Notation "'do' X <- A ; B" := (bind A (fun X => B)) (at level 200, X ident, A at level 100, B at level 200).

Lemma mon_left_id : forall (A B : Type) (a : A) (f : A -> option B),
  ret a >>= f = f a.
intros.
reflexivity.
Qed.

Lemma mon_right_id : forall (A : Type) (a : option A),
  a >>= ret = a.
intros.
induction a; repeat reflexivity.
Qed.

Lemma mon_assoc :
  forall (A B C : Type) (a : option A) (f : A -> option B) (g : B -> option C),
    (a >>= f) >>= g = a >>= (fun x => f x >>= g).
intros.
induction a; repeat reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)

Definition name_t : Type := string.


(* ------------------------------------------------------------------------- *)

Inductive type_t : Type :=
  | Integer : type_t
  | Nil : type_t 
  | Ref : type_t -> type_t
  | Array : nat ->  type_t -> type_t.

Fixpoint type_eqb (a b : type_t) : bool :=
  match a, b with
  | Integer, Integer => true
  | Nil, Nil => true
  | Ref ta, Ref tb => type_eqb ta tb
  | Array la ta, Array lb tb => Nat.eqb la lb && type_eqb ta tb
  | _, _ => false
  end.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)

Theorem type_eqb_refl : forall (a: type_t),
  type_eqb a a = true.
Proof.
  intros.
  induction a; simpl; try reflexivity; try apply IHa.
  - rewrite PeanoNat.Nat.eqb_refl. simpl. apply IHa.
Qed.


(* ------------------------------------------------------------------------- *)

Inductive value_t : Type :=
  | Int : nat -> value_t
  | Null : value_t.

Definition value_eqb (a b : value_t) : bool :=
  match a, b with
  | Int a, Int b => Nat.eqb a b
  | Null, Null => true
  | _, _ => false
  end.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)

Theorem value_eqb_refl : forall (a: value_t),
  value_eqb a a = true.
Proof.
  intros.
  destruct a; unfold value_eqb.
  - apply PeanoNat.Nat.eqb_refl.
  - reflexivity.
Qed.


(* ------------------------------------------------------------------------- *)

Inductive definition_t : Type :=
  | Inclusion : definition_t
  | Const : value_t -> definition_t
  | TypeDef : type_t -> definition_t
  | Var : type_t -> definition_t.

Definition definition_eqb (a b: definition_t) : bool :=
  match a, b with
  | Inclusion, Inclusion => true
  | TypeDef ta, TypeDef tb => type_eqb ta tb
  | Var ta, Var tb => type_eqb ta tb
  | Const va, Const vb => value_eqb va vb
  | _, _ => false
  end.

Definition definition_is_type (d: definition_t) : bool :=
  match d with
  | TypeDef _ => true
  | _ => false
  end.

Definition definition_redefines (a b: definition_t) : bool :=
  match a, b with
  | TypeDef ta, TypeDef tb => type_eqb ta tb
  | Var ta, Var tb         => type_eqb ta tb
  | Const va, Const vb     => value_eqb va vb
  | Inclusion, Inclusion   => true
  | _, _                   => false
  end.

Definition definition_redefine (a b: definition_t) : option definition_t :=
  some_if b (definition_redefines a b).

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)

Theorem definition_eqb_refl : forall (a: definition_t),
  definition_eqb a a = true.
Proof.
  intros.
  destruct a; unfold definition_eqb; 
  try reflexivity; 
  try apply value_eqb_refl;
  try apply type_eqb_refl.
Qed.

Theorem definition_redefines_self : forall (a: definition_t),
  definition_redefine a a = Some a.
Proof.
  intros.
  destruct a; unfold definition_redefine; apply some_if_true; simpl. 
  - reflexivity.
  - apply value_eqb_refl.
  - apply type_eqb_refl.
  - apply type_eqb_refl.
Qed.


(* ------------------------------------------------------------------------- *)


Module Contents := MMaps.RBT.Make String_as_OT.

Definition interface_t : Type := Contents.t definition_t. 

Definition empty_interface : interface_t := Contents.empty.

Definition add_definition (i: interface_t) (n: name_t) (d: definition_t) : option interface_t :=
  match Contents.find n i with
  | None => Some (Contents.add n d i)
  | Some d' =>
    do d'' <- definition_redefine d' d;
    ret (Contents.add n d'' i)
  end.

Definition add_definition_acc (n: name_t) (d: definition_t)  (acc: option interface_t) : option interface_t :=
  do i <- acc; add_definition i n d.

Definition add_interface (dst src: interface_t) : option interface_t :=
  Contents.fold add_definition_acc src (Some dst).

Definition contains_definition
    (i: interface_t) 
    (n: name_t) 
    (d: definition_t) : bool :=
  match Contents.find n i with
  | Some dm =>  definition_eqb dm d
  | None => false
  end.

Definition contains_definition_acc 
    (i: interface_t) 
    (n: name_t) (d: definition_t) (acc: bool) : bool :=
  acc && contains_definition i n d.

Definition includes (i sub: interface_t) : bool :=
  Contents.fold (contains_definition_acc i) sub true.

(* - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - *)

Theorem adding_to_empty_works : 
  forall (i: interface_t) (n: name_t) (d: definition_t),
  add_definition Contents.empty n d = Some(i) -> 
  contains_definition i n d = true.
Proof.
  intros.
  unfold add_definition in H. 
  simpl in H. 
  inversion H.
  unfold contains_definition. 
  rewrite Contents.add_spec1. 
  apply definition_eqb_refl.
Qed.

Theorem a : 
  forall  (i j: interface_t) (n: name_t) (d: definition_t),
  add_definition i n d = Some(j) -> 
  contains_definition j n d = true.
Proof.
  intros.
  unfold contains_definition. simpl.
  unfold add_definition in H.
  destruct (Contents.find n i).
  - destruct (definition_eqb dm d).
  
