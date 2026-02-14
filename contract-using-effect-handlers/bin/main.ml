open Effect.Deep

let () = print_endline "Hello, World!"

exception Wrong of string

let f = fun x ->
  let module Local = struct
    type _ Effect.t += CheckParam1 : int -> unit Effect.t
    type _ Effect.t += CheckReturn : int -> unit Effect.t
  end in
  let predicate_1 v = v > 10 in
  let predicate_ret v = v > 20 in
  match
    Effect.perform (Local.CheckParam1 x);
    let ret = x + 1 in
    Effect.perform (Local.CheckReturn ret);
    ret
  with
  | res -> res
  | effect (Local.CheckParam1 v), k ->
      Printf.printf "F Check Param 1: %d\n" v;
      if (predicate_1 v)
      then continue k ()
      else discontinue k (Wrong "F Param 1 Not Good")
  | effect (Local.CheckReturn v), k ->
      Printf.printf "F Check Return Value: %d\n" v;
      if (predicate_ret v)
      then continue k ()
      else discontinue k (Wrong "F Return Value Not Good")

let g = fun f ->
  (* g can specify signature for f too
     we wrap f again, by default, it should perform as we would
     expect in normal contract checking
   *)
  let f_binded = fun x ->
    let module Local = struct
      type _ Effect.t += CheckParam1 : int -> unit Effect.t
      type _ Effect.t += CheckReturn : int -> unit Effect.t
    end in
    let predicate_1 v = v < 15 in
    let predicate_ret v = v < 25 in
    match
      Effect.perform (Local.CheckParam1 x);
      let ret = f x in
      Effect.perform (Local.CheckReturn ret);
      ret
    with
    | res -> res
    | effect (Local.CheckParam1 v), k ->
        Printf.printf "G Check Param 1: %d\n" v;
        if (predicate_1 v)
        then continue k ()
        else discontinue k (Wrong "G Param 1 Not Good")
    | effect (Local.CheckReturn v), k ->
        Printf.printf "G Check Return Value: %d\n" v;
        if (predicate_ret v)
        then continue k ()
        else discontinue k (Wrong "G Return Value Not Good")
  in
  f_binded 16

let () =
  let _ = g f in
  ()
