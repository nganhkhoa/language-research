let bigger_than_10 x = x > 10

let [@contract] run
  (x : int [@pred : bigger_than_10])
  : int [@pred : bigger_than_10] =
  x

let [@contract] run_function
  (f : int -> int [@pred : bigger_than_10 -> bigger_than_10])
  (x : int [@pred : bigger_than_10])
  : int [@pred : bigger_than_10]
  =
    (* originally
         f x
       because f is a function (we know from the type signature)
       we build a wrapped version, only if it is annotated with
       a contract; else we leave f as is
       because of f isolation, we can make parameter names for it
       p1 p2 p3 ...
     *)
  let [@contract] f_wrapped
    (p1 : int [@pred : bigger_than_10])
    : int [@pred : bigger_than_10]
    = f p1
  in
  f_wrapped x

(* by transformation we expect it to build in multiple phases due to how
   traversal works

   1st phase resolves everything that is not a function
   for every parameters that are functions, build a wrapped version
   replace all their references into the corresponding wrapped version

   let run_function =
     let module Local = struct
       type _ Effect.t += CheckParam_x : int -> unit Effect.t
       type _ Effect.t += CheckReturn : int -> unit Effect.t
     end in

     let [@contract] f_wrapped
       (param1 : int [@pred bigger_than_10])
       : int [@pred bigger_than_10]
     = f param1 param2 ...
     in
     match
       (* body of run_function *)
       f_wrapped x
     with
     | res -> res
     | effect AllowedEffects, k -> ...

     | effect e, k ->
       match e with
       | CheckParam_x v ->
           let checked = match pred_x with
           | AllowedEffectsInContract -> ...
           in
           if checked
           then continue k ()
           else discontinue k (Blame "?")

    2nd phase expands wrapped versions using the same logic
    repeated until all functions appearing as argument are wrapped
    exception: if the user don't specify the contract, then we don't attach
    contract handler

    effects scoping clashing each other? will try with multi-layer and see
    but I expect that it is not gonna happen because each of them
    uses a different handler

    we only get problem when using handler inside a handler
 *)

(* let () =
  let open Sample_code in
  run_test *)
