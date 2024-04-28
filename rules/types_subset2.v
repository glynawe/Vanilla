(* A larger subset of the Vanilla type rules in Gallina. *)

(* (Recursively defined Tuple type.) *)
(* (Vanilla uses records, but they are tuples here just for simplicity. *)
 
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope bool_scope.


Inductive vanilla_t : Type :=
  | Integer
  | Boolean
  | Ref (rt: vanilla_t)
  | Nil
  | Array (length: nat) (element: vanilla_t)
  | OpenArray (element: vanilla_t)
  | Tuple (elements: list vanilla_t).


Fixpoint equal (t1: vanilla_t) (t2: vanilla_t) : bool :=
  match t1, t2 with
  | Integer, Integer => true
  | Boolean, Boolean => true
  | Nil, Nil => true
  | Ref rt1, Ref rt2 => equal rt1 rt2  
  | Array len1 et1, Array len2 et2 => Nat.eqb len1 len2 && equal et1 et2
  | OpenArray et1, OpenArray et2 => equal et1 et2
  | Tuple es1, Tuple es2 =>
    (fix equal_elements xs ys :=   (* this has to be nested ! *)
      match xs, ys with
      | t1 :: xs', t2 :: ys' => equal t1 t2 && equal_elements xs' ys'
      | nil, nil => true
      | _, _ => false
      end
    ) es1 es2
  | _, _ => false 
  end.


Fixpoint valid_variable (t: vanilla_t) : bool :=
  match t with
  | Integer => true
  | Boolean => true
  | Ref rt => valid_reference rt
  | Nil => false
  | Array len et => Nat.ltb 0 len && valid_variable et
  | OpenArray _ => false
  | Tuple es => forallb valid_variable es
  end

with valid_reference (t: vanilla_t) : bool :=
  match t with
  | Integer => true
  | Boolean => true
  | Ref rt => valid_reference rt
  | Nil => false
  | Array len et => Nat.ltb 0 len && valid_variable et
  | OpenArray a => valid_variable a
  | Tuple es => forallb valid_variable es
  end.

Definition valid_value (t: vanilla_t) : bool :=
  match t with
  | Integer => true
  | Boolean => true
  | Ref rt => valid_reference rt
  | Nil => true
  | Array _ _ => false
  | OpenArray _ => false
  | Tuple _ => false
  end.


Definition assignment_compatible (dst: vanilla_t) (src: vanilla_t) : bool :=
  match dst, src with
  | Ref _,       Nil         => true
  | Nil,         _           => false
  | OpenArray _, _           => false
  | _,           OpenArray _ => false
  | t1,          t2          => equal t1 t2
  end.

Definition var_parameter_compatible (dst: vanilla_t) (src: vanilla_t) : bool :=
  match dst, src with
  | OpenArray et1,  Array _ et2  => equal et1 et2
  | t1,             t2           => equal t1 t2
  end.

Definition value_parameter_compatible (dst: vanilla_t) (src: vanilla_t) : bool :=
  match dst, src with
  | OpenArray et1,  Array _ et2    => equal et1 et2
  | OpenArray et1,  OpenArray et2  => equal et1 et2
  | t1,             t2             => assignment_compatible t1 t2
  end.
