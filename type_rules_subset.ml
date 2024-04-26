(* A subset of the Vanilla type rules in OCaml. *)

type t =
  | Integer
  | Boolean
  | Ref of t
  | Nil
  | Array of int * t
  | OpenArray of t


let rec equal (a: t) (b: t): bool =
  match a, b with
  | Integer, Integer
  | Boolean, Boolean
  | Nil, Nil -> true
  | Ref rt1, Ref rt2 -> equal rt1 rt2
  | Array (len1, et1), Array (len2, et2) -> len1 = len2 && equal et1 et2
  | OpenArray et1, OpenArray et2 -> equal et1 et2
  | _ -> false


let rec valid_variable (a: t) : bool =
  match a with
  | Integer -> true
  | Boolean -> true
  | Ref rt -> valid_reference rt
  | Nil -> false
  | Array (d, et) -> d > 0 && valid_variable et
  | OpenArray _ -> false

and valid_reference (a: t) : bool =
  match a with
  | Integer -> true
  | Boolean -> true
  | Ref rt -> valid_reference rt
  | Nil -> false
  | Array (d, et) -> d > 0 && valid_variable et
  | OpenArray et -> valid_variable et

let valid_value (a: t) : bool =
  match a with
  | Integer -> true
  | Boolean -> true
  | Ref rt -> valid_reference rt
  | Nil -> true
  | Array (_, _) -> false
  | OpenArray _ -> false


let assignment_compatible (dst: t) (src: t) : bool =
  match dst, src with
  | Ref _,       Nil          -> true
  | Nil ,        _            -> false
  | OpenArray _, _            -> false
  | _,           OpenArray _  -> false
  | t1,          t2           -> equal t1 t2

let var_parameter_compatible (dst: t) (src: t) : bool =
  match dst, src with
  | OpenArray et1, Array (_, et2) -> equal et1 et2
  | t1,            t2             -> equal t1 t2

let value_parameter_compatible (dst: t) (src: t) : bool =
  match dst, src with
  | OpenArray et1, Array (_, et2) -> equal et1 et2
  | OpenArray et1, OpenArray et2  -> equal et1 et2
  | t1,            t2             -> assignment_compatible t1 t2
