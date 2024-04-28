(* A subset of the Vanilla type rules in Gallina. *)
(* (No recursively defined types.) *)
 
Inductive vanilla_t : Type :=
  | Integer
  | Boolean
  | Ref (rt: vanilla_t)
  | Nil
  | Array (length: nat) (element: vanilla_t)
  | OpenArray (element: vanilla_t).


Fixpoint equal (t1: vanilla_t) (t2: vanilla_t) : bool :=
  match t1, t2 with
  | Integer, Integer => true
  | Boolean, Boolean => true
  | Nil, Nil => true
  | Ref rt1, Ref rt2 => equal rt1 rt2  
  | Array len1 et1, Array len2 et2 => Nat.eqb len1 len2 && equal et1 et2
  | OpenArray et1, OpenArray et2 => equal et1 et2
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
  end

with valid_reference (t: vanilla_t) : bool :=
  match t with
  | Integer => true
  | Boolean => true
  | Ref rt => valid_reference rt
  | Nil => false
  | Array len et => Nat.ltb 0 len && valid_variable et
  | OpenArray a => valid_variable a
  end.

Definition valid_value (t: vanilla_t) : bool :=
  match t with
  | Integer => true
  | Boolean => true
  | Ref rt => valid_reference rt
  | Nil => true
  | Array _ _ => false
  | OpenArray _ => false
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
