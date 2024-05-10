(* A subset of Vanilla's module system and top-level defs. *)


module type EQUALITY = sig
  type t
  val equal : t -> t -> bool
end


module Type (Name: EQUALITY) (GlobalName: EQUALITY) =
struct
  type t =
  | Integer
  | Nil
  | Ref of t
  | Array of int * t
  | Abstract of GlobalName.t
  | Record of (Name.t * t) list

  let rec equal (a: t) (b: t) : bool = 
    match a, b with
    | Integer, Integer -> true
    | Nil, Nil -> true
    | Ref ta, Ref tb -> equal ta tb
    | Array (la, ta), Array (lb, tb) -> la = lb && equal ta tb
    | Abstract na, Abstract nb -> GlobalName.equal na nb
    | Record ra, Record rb -> List.for_all2 equal_elements ra rb 
    | _, _ -> false
  and equal_elements (na, ta) (nb, tb) =
    Name.equal na nb && equal ta tb
end


module Value =
struct 
  type t =
  | Integer of int
  | Nil
  (* etc *)

  let value_equal (a: t) (b: t) : bool =
    match a, b with
    | Integer a', Integer b' -> a' = b'
    | Nil, Nil -> true
    | _, _ -> false
end


module Definition (Name: EQUALITY) (Value: EQUALITY) (Type: EQUALITY) =
struct 
  type t =   
  | Type of Type.t
  | Var of Type.t
  | Val of Type.t
  | Const of Type.t * Value.t
  | Procedure of Name.t list * Type.t

  let equal (a: t) (b: t) : bool =
  match a, b with
  | Type ta, Type tb -> Type.equal ta tb
  | Var ta, Var tb -> Type.equal ta tb
  | Val ta, Val tb -> Type.equal ta tb
  | Const (ta, va), Const (tb, vb) -> 
      Type.equal ta tb && Value.equal va vb
  | Procedure (pa, ta), Procedure (pb, tb) -> 
      Type.equal ta tb && List.length pa = List.length pb 
  | _, _ -> false
end


module Module (GlobalName: Map.OrderedType) (Definition: EQUALITY) =
struct
  module Contents = Map.Make(GlobalName)

  type t = Definition.t Contents.t

  let equal (a: t) (b: t) : bool =
    Contents.equal Definition.equal a b

  let add_definition (m: t) (n: GlobalName.t) (d: Definition.t) : t option =
    match Contents.find_opt n m with
    | None -> Some (Contents.add n d m)
    | Some dm when Definition.equal dm d -> Some m
    | Some _ -> None

  let add_interface (m: t) (i: t) : t option =
    Utility.OptionMonad.fold_option
      (fun m (n, d) -> add_definition m n d) m (Contents.bindings i)
        
  let contains_definition (m: t) (n: GlobalName.t) (d: Definition.t) : bool =
    match Contents.find_opt n m with
    | Some dm -> Definition.equal dm d
    | None -> false

  let contains_interface (m: t) (i: t) : bool =
    Contents.for_all (contains_definition m) i
end
