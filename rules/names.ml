module type NAME = 
sig
  type t
  val equal : t -> t -> bool
  val compare : t -> t -> int
end

module type GLOBALNAME = 
sig
  type name_t
  type t = 
  | Local of name_t
  | Imported of name_t * name_t
  val equal : t -> t -> bool
  val compare : t -> t -> int 
end

module Name : NAME = struct
  type t = string
  let equal = String.equal
  let compare = String.compare
end

module NamePair = struct
  type t = Name.t * Name.t
  let compare (x0,y0) (x1,y1) =
    match Name.compare x0 x1 with
        0 -> Name.compare y0 y1
      | c -> c
end

module NamePairs = Set.Make(NamePair)

module Table = Map.Make(Name)

module Equivalents = struct
  type t = NamePairs.t
  let empty = NamePairs.empty 
  let equivalent e a b = NamePairs.mem (a, b) e || NamePairs.mem (b, a) e
  let add_equivalence e a b = e |> NamePairs.add (a, b) |> NamePairs.add (b, a)
end

module Globalname : GLOBALNAME with type name_t = Name.t = struct
  type name_t = Name.t
  type t = 
  | Local of name_t
  | Imported of name_t * name_t
  
  let equal a b =
    match a, b with
    | Local n1, Local n2 -> Name.equal n1 n2
    | Imported (m1, n1), Imported (m2, n2) -> Name.equal m1 m2 && Name.equal n1 n2
    | _, _ -> false
  
  let compare a b =
    match a, b with
    | Local n1, Local n2 -> Name.compare n1 n2
    | Imported (m1, n1), Imported (m2, n2) ->
        let i = Name.compare m1 m2 in
        if i = 0 then Name.compare n1 n2 else i 
    | Imported (m1, n1), Local n2 ->
        let i = Name.compare m1 n2 in
        if i = 0 then Name.compare n1 n2 else i 
    | Local n1, Imported (m2, n2) ->
        let i = Name.compare n1 m2 in
        if i = 0 then Name.compare n1 n2 else i 
end
