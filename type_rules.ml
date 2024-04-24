(* The Vanilla type rules in OCaml. These will later be defined in Gallina for Coq proofs. *)


(* Identifiers. (Note: this is a dumy, Name.t and Name.equal will be defined elsewhere.) *)
module Name = struct
  type t = string
  let equal = String.equal
end


(* ------------------------------------------------------------------------------- *)
(* Types *)
(* ------------------------------------------------------------------------------- *)


type t =
  | Integer
  | Byte
  | Word
  | Real
  | Boolean
  | Statement                     (* The type of statements. (Like C's void.) *)
  | Ref of t
  | Nil                           (* compatable with any reference *)
  | Array of int * t
  | OpenArray of t                (* Array whose length is only known at runtime.*)
  | Record of (Name.t * t) list
  | Procedure of parameter_t list * t

and parameter_t = 
  |  VarParameter of Name.t * t
  |  ValParameter of Name.t * t


type procedure_call_t = 
  Call of call_parameter_t list

and call_parameter_t =
  | SuppliedValue of t
  | SuppliedDesignator of t



(* ------------------------------------------------------------------------------- *)
(* Type Equality *)
(* ------------------------------------------------------------------------------- *)


(** [equal a b] True if types [a] and [b] are equal by structural equivalence. *)

let rec equal a b =  
  match a, b with
  | Integer, Integer
  | Byte, Byte
  | Word, Word
  | Real, Real
  | Boolean, Boolean
  | Nil, Nil
  | Statement, Statement -> true
  | Ref t1, Ref t2 when equal t1 t2 -> true  
  | Array (len1, t1), 
    Array (len2, t2) when len1 = len2 && equal t1 t2 -> true
  | Procedure (p1, t1), 
    Procedure (p2, t2) when equal_parameters p1 p2 && equal t1 t2 -> true
  | OpenArray t1, 
    OpenArray t2 when equal t1 t2 -> true
  | Record e1, 
    Record e2 when equal_elements e1 e2 -> true 
  | _ -> false 

(* Lists of procedure parameters are equal if the parameters from each list be paired, 
    and each pair of parameters has an equal mutability and type. 
    (Parameter names are ignored, they are just placeholders.) *)
 
and equal_parameters p1 p2 =
  match p1, p2 with
  | VarParameter (_, t1) :: p1', 
    ValParameter (_, t2) :: p2' when equal t1 t2 -> equal_parameters p1' p2'
  | ValParameter (_, t1) :: p1', 
    VarParameter (_, t2) :: p2' when equal t1 t2 -> equal_parameters p1' p2'
  | [], [] -> true
  | _ -> false

(* Lists of record elements are equal if the elements from each list be paired, 
    and each pair of elements has the an equal name and equal type. *)

and equal_elements e1 e2 =
  match e1, e2 with
  | (n1, t1) :: e1', 
    (n2, t2) :: e2' when Name.equal n1 n2 && equal t1 t2 -> equal_elements e1' e2'
  | (n1, t1) :: e1', 
    (n2, t2) :: e2' when Name.equal n1 n2 && equal t1 t2 -> equal_elements e1' e2'
  | [], [] -> true
  | _ -> false


(* ------------------------------------------------------------------------------- *)
(* Type Validity *)
(* ------------------------------------------------------------------------------- *)


(** [valid_value a] is true if type [a] is an acceptable expression value.  *)

let rec valid_value a =
  match a with
  | Nil -> true
  | Statement -> false 
  | a -> valid_variable a 


(** [valid_target a] is true if type [a] can be used as a reference type target 
    or a procedure parameter. *)

and valid_target a =
  match a with
  | OpenArray a -> valid_variable a
  | a -> valid_variable a 


(** [valid_variable a] is true if type [a] is can be stored in a variable,
    is assignable and is otherwise generally valid.  *)

and valid_variable a = 
  match a with
  | Integer | Byte | Word | Real | Boolean -> true
  | Ref b -> valid_target b
  | Array (d, e) -> d > 0 && valid_variable e
  | OpenArray _ | Statement | Nil -> false
  | Procedure (ps, rt) -> 
      let ptype p = 
        match p with 
        | VarParameter (_, pt) -> pt
        | ValParameter (_, pt) -> pt
      in
      List.for_all valid_target (List.map ptype ps) 
      && valid_return_type rt
  | Record es -> 
      let (ns, ts) = List.split es in
      let rec all_different =  (* for checking element names *)
        function
        | [] -> true
        | n :: ns -> not (List.exists (Name.equal n) ns) && all_different ns
      in
      List.length es > 0 && all_different ns 
      && List.for_all valid_variable ts 
 

(** [valid_return_type a] is true if type [a] can be used as a procedure return type. *)

and valid_return_type a = (a = Nil) || valid_value a


(* ------------------------------------------------------------------------------- *)
(* Assignment Compatabilities *)
(* ------------------------------------------------------------------------------- *)


(** [assignment_compatable dst src] is true if a variable of type [dst] can be
    assigned a value of type [src]. 

    Two types are usually assignment compatable if they have equal types.
    The exceptions are that any reference can be assigned nil and a reference 
    to a procedure can be assigned an procedure. But otherwise open arrays, 
    procedures and statements cannot be assigned. *)

let assignment_compatable dst src =
  match dst, src with
  | Ref _, Nil -> true
  | Ref (Procedure (_, _) as a), (Procedure (_, _) as b) -> equal a b
  | (Nil | OpenArray _ | Statement | Procedure (_,_)), _ -> false 
  | _, (Nil | OpenArray _ | Statement | Procedure (_,_)) -> false 
  | t1, t2 -> equal t1 t2
    

(** [var_parameter_compatable dst src] is true if a designator of type
    [src] can by supplid to porocedure parameter of type [dst].contents

    An supplied parameter is type compatible with a 'var' formal parameter if 
    their types are equal. The exception is that open arrays are compatible 
    with arrays if their element types are equal. *)

let var_parameter_compatable dst src =
  match dst, src with
  | OpenArray t1, Array (_, t2) when equal t1 t2 -> true
  | OpenArray t1, OpenArray t2 when equal t1 t2 -> true
  | t1, t2 -> equal t1 t2
  

(** [var_parameter_type_compatable dst src] is true if a designator of type
    [src] can by supplid to porocedure parameter of type [dst].contents

    An supplied parameter is type compatible with a 'var' formal parameter if 
    their types are equal. The exception is that open arrays are compatible 
    with arrays if their element types are equal. *)

let val_parameter_compatable dst src =
  match dst, src with
  | OpenArray t1, Array (_, t2) when equal t1 t2 -> true
  | OpenArray t1, OpenArray t2 when equal t1 t2 -> true
  | t1, t2 -> assignment_compatable t1 t2


(* ------------------------------------------------------------------------------- *)
(* Procedure Call Validity *)
(* ------------------------------------------------------------------------------- *)


(** [procedure_call_valid procedure_type call_parameters] is true if
    there are the same number of [call_parameters] as [procedure_type]
    parameters, var parameters are not supplied values, and the types of each 
    pair of procedure parameter and supplied parameter are compatible. *)  

let procedure_call_valid (Procedure (procedure_parameters, _)) call_parameters =
  let parameter_compatable (p, s) =
    match p, s with
    | ValParameter (_, pt), SuppliedValue      st -> val_parameter_compatable pt st 
    | ValParameter (_, pt), SuppliedDesignator st -> val_parameter_compatable pt st 
    | VarParameter (_, pt), SuppliedValue      st -> false
    | VarParameter (_, pt), SuppliedDesignator st -> var_parameter_compatable pt st
  in
  List.length procedure_parameters = List.length call_parameters &&
  List.for_all parameter_compatable (List.combine procedure_parameters call_parameters)
