let rec distinct (equal: 't -> 't -> bool) (xs: 't list) : bool =
  match xs with
  | [] -> true
  | x :: xs' -> not (List.exists (equal x) xs') && distinct equal xs'

module OptionMonad = struct
  let (let*) = Option.bind
  let return = Option.some 

  let rec map_option (xs: 't list) (f: 't -> 'u option) : 'u list option =
    match xs with
    | [] -> return []
    | x :: xs' -> 
        let* y = f x in
        let* ys = map_option xs' f in 
        return (y :: ys)
;;
List.fold_left;;

  let rec fold_option  (f: 'u -> 't -> 'u option) (acc: 'u) (xs: 't list) : 'u option =
    match xs with
    | [] -> return acc
    | x :: xs' -> let* acc' = f acc x in fold_option f acc' xs' 

end